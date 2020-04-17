(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Sign
open Pos
open Files
open Syntax
open Scope

(* Register a check for the type of builtin successor symbol ["+1"]. *)
let _ =
  let expected_succ_type pos map =
    let typ_0 = lift !((Builtin.get pos map "0").sym_type) in
    Bindlib.unbox (_Impl typ_0 typ_0)
  in
  Builtin.register_expected_type (Eval.eq_modulo []) Print.term
    "+1" expected_succ_type

(** Representation of a yet unchecked proof. The structure is initialized when
    the proof mode is entered, and its finalizer is called when the proof mode
    is exited (i.e., when a terminator like “qed” is used).  Note that tactics
    do not work on this structure directly,  although they act on the contents
    of its [pdata_p_state] field. *)
type proof_data =
  { pdata_stmt_pos : Pos.popt (* Position of the proof's statement.  *)
  ; pdata_p_state  : Proof.t  (* Initial proof state for the proof.  *)
  ; pdata_tactics  : p_tactic list (* Tactics for the proof.         *)
  ; pdata_finalize : sig_state -> Proof.t -> sig_state (* Finalizer. *)
  ; pdata_term_pos : Pos.popt (* Position of the proof's terminator. *) }

(** [handle_open pos ss p] handles the command [open p] with [ss] as the
   signature state. On success, an updated signature state is returned. *)
let handle_open : popt -> sig_state -> Path.t -> sig_state =
    fun pos ss p ->
  (* Obtain the signature corresponding to [m]. *)
  let sign =
    try PathMap.find p !(Sign.loaded) with Not_found ->
      (* The signature has not been required... *)
      fatal pos "Module [%a] has not been required." Path.pp p
  in
  (* Open the module. *)
  open_sign ss sign

(** [handle_require b pos ss p] handles the command [require p] (or [require
   open p] if b is true) with [ss] as the signature state. On success, an
   updated signature state is returned. *)
let handle_require : bool -> popt -> sig_state -> Path.t -> sig_state =
    fun b pos ss p ->
  (* Check that the module has not already been required. *)
  if PathMap.mem p !(ss.signature.sign_deps) then
    fatal pos "Module [%a] is already required." Path.pp p;
  (* Add the dependency (it was compiled already while parsing). *)
  ss.signature.sign_deps := PathMap.add p [] !(ss.signature.sign_deps);
  if b then handle_open pos ss p else ss

(** [handle_require_as pos ss p id] handles the command [require p as id] with
   [ss] as the signature state. On success, an updated signature state is
   returned. *)
let handle_require_as : popt -> sig_state -> Path.t -> ident -> sig_state =
    fun pos ss p id ->
  let ss = handle_require false pos ss p in
  let aliases = StrMap.add id.elt p ss.aliases in
  {ss with aliases}

(** [handle_cmd_aux ss cmd] tries to handle the command [cmd] with [ss] as the
    signature state. On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
let handle_cmd : sig_state -> p_command -> sig_state * proof_data option =
  fun ss cmd ->
  let pp = Print.pp_term ss.hints in
  let pp_rule = Print.pp_rule ss.hints in
  let scope_basic exp = Scope.scope_term exp ss Env.empty in
  match cmd.elt with
  | P_require(b,ps)            ->
     let ps = List.map (List.map fst) ps in
     (List.fold_left (handle_require b cmd.pos) ss ps, None)
  | P_require_as(p,id)         ->
     let id = Pos.make id.pos (fst id.elt) in
     (handle_require_as cmd.pos ss (List.map fst p) id, None)
  | P_open(ps)                  ->
     let ps = List.map (List.map fst) ps in
     (List.fold_left (handle_open cmd.pos) ss ps, None)
  | P_symbol(e, p, x, xs, a) ->
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments of [a]. *)
      let a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
      (* Obtaining the implicitness of arguments. *)
      let impl = Scope.get_implicitness a in
      (* We scope the type of the declaration. *)
      let a = scope_basic e a in
      (* We check that [a] is typable by a sort. *)
      Typing.sort_type ss.builtins [] a;
      (* We check that no metavariable remains. *)
      if Basics.has_metas true a then
        begin
          fatal_msg "The type of [%s] has unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a." x.elt pp a
        end;
      (* Actually add the symbol to the signature and the state. *)
      let s = Sign.add_symbol ss.signature e p x a impl in
      out 3 "(symb) %s\n" s.sym_name;
      ({ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}, None)
  | P_rules(rs)                ->
      (* Scoping and checking each rule in turn. *)
      let handle_rule r =
        let pr = scope_rule ss r in
        let sym = pr.elt.pr_sym in
        if !(sym.sym_def) <> None then
          fatal pr.pos "Rewriting rules cannot be given for defined \
                        symbol [%s]." sym.sym_name;
        (sym, Pos.make r.pos (Sr.check_rule ss.builtins pr))
      in
      let rs = List.map handle_rule rs in
      (* Adding the rules all at once. *)
      let add_rule (s,r) =
        Sign.add_rule ss.signature s r.elt;
        out 3 "(rule) %a\n" pp_rule (s,r.elt)
      in
      List.iter add_rule rs;
      let syms = List.remove_phys_dups (List.map (fun (s, _) -> s) rs) in
      List.iter Tree.update_dtree syms;
      (ss, None)
  | P_definition(e,op,x,xs,ao,t) ->
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments and scoping of [t]. *)
      let t = if xs = [] then t else Pos.none (P_Abst(xs, t)) in
      let t = scope_basic e t in
      (* Desugaring of arguments and computation of argument impliciteness. *)
      let (ao, impl) =
        match ao with
        | None    -> (None, List.map (fun (_,_,impl) -> impl) xs)
        | Some(a) ->
            let a = if xs = [] then a else Pos.none (P_Prod(xs,a)) in
            (Some(a), Scope.get_implicitness a)
      in
      let ao = Option.map (scope_basic e) ao in
      (* If a type [a] is given, then we check that [a] is typable by a sort
         and that [t] has type [a]. Otherwise, we try to infer the type of
         [t] and return it. *)
      let a =
        match ao with
        | Some(a) ->
            Typing.sort_type ss.builtins [] a;
            if Typing.check ss.builtins [] t a then a else
              fatal cmd.pos "The term [%a] does not have type [%a]." pp t pp a
        | None    ->
            match Typing.infer ss.builtins [] t with
            | Some(a) -> a
            | None    -> fatal cmd.pos "Cannot infer the type of [%a]." pp t
      in
      (* We check that no metavariable remains. *)
      if Basics.has_metas true t || Basics.has_metas true a then
        begin
          fatal_msg "The definition of [%s] or its type \
                     have unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a ≔ %a." x.elt pp a pp t
        end;
      (* Actually add the symbol to the signature. *)
      let d = if op then None else Some(t) in
      let ss = Scope.add_symbol ss e Defin x a impl d in
      out 3 "(symb) %s ≔ %a\n" x.elt pp t;
      (ss, None)
  | P_theorem(e, stmt, ts, pe) ->
      let (x,xs,a) = stmt.elt in
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments of [a]. *)
      let a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
      (* Obtaining the implicitness of arguments. *)
      let impl = Scope.get_implicitness a in
      (* Scoping the type (statement) of the theorem. *)
      let a = scope_basic e a in
      (* Check that [a] is typable and that its type is a sort. *)
      Typing.sort_type ss.builtins [] a;
      (* We check that no metavariable remains in [a]. *)
      if Basics.has_metas true a then
        begin
          fatal_msg "The type of [%s] has unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a." x.elt pp a
        end;
      (* Initialize proof state and save configuration data. *)
      let st = Proof.init ss.builtins x a in
      Console.push_state ();
      (* Build proof checking data. *)
      let finalize ss st =
        Console.pop_state ();
        match pe.elt with
        | P_proof_abort ->
            (* Just ignore the command, with a warning. *)
            wrn cmd.pos "Proof aborted."; ss
        | P_proof_admit ->
            (* If the proof is finished, display a warning. *)
            if Proof.finished st then
              wrn cmd.pos "The proof is finished. You can use 'qed' instead.";
            (* Add a symbol corresponding to the proof, with a warning. *)
            out 3 "(symb) %s (admit)\n" x.elt;
            wrn cmd.pos "Proof admitted.";
            Scope.add_symbol ss e Const x a impl None
        | P_proof_qed   ->
            (* Check that the proof is indeed finished. *)
            if not (Proof.finished st) then
              begin
                let _ = Tactics.handle_tactic ss st (none P_tac_print) in
                fatal cmd.pos "The proof is not finished."
              end;
            (* Add a symbol corresponding to the proof. *)
            out 3 "(symb) %s (qed)\n" x.elt;
            Scope.add_symbol ss e Const x a impl None
      in
      let data =
        { pdata_stmt_pos = stmt.pos ; pdata_p_state = st ; pdata_tactics = ts
        ; pdata_finalize = finalize ; pdata_term_pos = pe.pos }
      in
      (ss, Some(data))
  | P_set(cfg)                 ->
      let ss =
        match cfg with
        | P_config_builtin(s,qid) ->
            (* Set the builtin symbol [s]. *)
            if StrMap.mem s ss.builtins then
              fatal cmd.pos "Builtin [%s] already exists." s;
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            Builtin.check cmd.pos ss.builtins s sym;
            Sign.add_builtin ss.signature s sym;
            out 3 "(conf) set builtin [%s]\n" s;
            {ss with builtins = StrMap.add s sym ss.builtins}
        | P_config_unop(unop)     ->
            let (s, _, qid) = unop in
            (* Define the unary operator [s]. *)
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            out 3 "(conf) new prefix [%s]\n" s;
            Scope.add_unop ss s (sym, unop)
        | P_config_binop(binop)   ->
            let (s, _, _, qid) = binop in
            (* Define the binary operator [s]. *)
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            out 3 "(conf) new infix [%s]\n" s;
            Scope.add_binop ss s (sym, binop)
        | P_config_ident(id)      ->
            Sign.add_ident ss.signature id;
            out 3 "(conf) declared identifier [%s]\n" id; ss
      in
      (ss, None)
  | P_query(q)                 ->
      Queries.handle_query ss None q; (ss, None)

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Stdlib.ref infinity

(** [handle_cmd ss cmd] is similar to [handle_cmd_aux ss cmd] but it adds some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle_cmd : sig_state -> p_command -> sig_state * proof_data option =
    fun ss cmd ->
  try
    let (tm, ss) = time (handle_cmd ss) cmd in
    if Stdlib.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           ->
      fatal cmd.pos "Uncaught exception [%s]." (Printexc.to_string e)
