(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Print
open Sign
open Pos
open Files
open Syntax
open Scope

(** [check_builtin_nat s] checks that the builtin symbol [s] for
   non-negative literals has a good type. *)
let check_builtin_nat : popt -> sym StrMap.t -> string -> sym -> unit
  = fun pos builtins s sym ->
  match s with
  | "+1" ->
     let builtin = Sign.builtin pos builtins in
     let symb_0 = builtin "0" in
     let typ_0 = !(symb_0.sym_type) in
     let x = Bindlib.new_var mkfree "_" in
     let typ_s = Ctxt.to_prod [(x, typ_0)] typ_0 in
     if not (Basics.eq typ_s !(sym.sym_type)) then
       fatal pos "The type of [%s] is not of the form [%a]"
         sym.sym_name pp typ_s
  | _ -> ()

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

(** [handle_cmd_aux ss cmd] tries to handle the command [cmd] with [ss] as the
    signature state. On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
let handle_cmd_aux : sig_state -> command -> sig_state * proof_data option =
    fun ss cmd ->
  let scope_basic ss t = fst (Scope.scope_term StrMap.empty ss Env.empty t) in
  match cmd.elt with
  | P_require(p, m)            ->
      (* Check that the module has not already been required. *)
      if PathMap.mem p !(ss.signature.sign_deps) then
        fatal cmd.pos "Module [%a] is already required." pp_path p;
      (* Add the dependency (it was compiled already while parsing). *)
      ss.signature.sign_deps := PathMap.add p [] !(ss.signature.sign_deps);
      (* Open or alias if necessary. *)
      let ss =
        match m with
        | P_require_default -> ss
        | P_require_open    ->
            let sign =
              try PathMap.find p !(Sign.loaded)
              with Not_found -> assert false (* Cannot happen. *)
            in
            open_sign ss sign
        | P_require_as(id)  ->
            let aliases = StrMap.add id.elt p ss.aliases in
            {ss with aliases}
      in
      (ss, None)
  | P_open(m)                  ->
      (* Obtain the signature corresponding to [m]. *)
      let sign =
        try PathMap.find m !(Sign.loaded) with Not_found ->
        (* The signature has not been required... *)
        fatal cmd.pos "Module [%a] has not been required." pp_path m
      in
      (* Open the module. *)
      (open_sign ss sign, None)
  | P_symbol(ts, x, xs, a)     ->
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments of [a]. *)
      let a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
      (* Obtaining the implicitness of arguments. *)
      let impl = Scope.get_implicitness a in
      (* We scope the type of the declaration. *)
      let a = scope_basic ss a in
      (* We check that [a] is typable by a sort. *)
      Typing.sort_type ss.builtins Ctxt.empty a;
      (* We check that no metavariable remains. *)
      if Basics.has_metas a then
        begin
          fatal_msg "The type of [%s] has unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a." x.elt pp a
        end;
      (* We build the symbol declaration mode from the tags. *)
      let m =
        match ts with
        | []              -> Defin
        | Sym_const :: [] -> Const
        | Sym_inj   :: [] -> Injec
        | _               -> fatal cmd.pos "Multiple symbol tags."
      in
      (* Actually add the symbol to the signature and the state. *)
      let s = Sign.add_symbol ss.signature m x a impl in
      out 3 "(symb) %s.\n" s.sym_name;
      ({ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}, None)
  | P_rules(rs)                ->
      (* Scoping and checking each rule in turn. *)
      let handle_rule r =
        let (s,_,_) as r = scope_rule ss r in
        if !(s.sym_def) <> None then
          fatal_no_pos "Symbol [%s] cannot be (re)defined." s.sym_name;
        Sr.check_rule ss.builtins r; r
      in
      let rs = List.map handle_rule rs in
      (* Adding the rules all at once. *)
      let add_rule (s,h,r) =
        out 3 "(rule) %a\n" Print.pp_rule (s,h,r.elt);
        Sign.add_rule ss.signature s r.elt
      in
      List.iter add_rule rs; (ss, None)
  | P_definition(op,x,xs,ao,t) ->
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments and scoping of [t]. *)
      let t = if xs = [] then t else Pos.none (P_Abst(xs, t)) in
      let t = scope_basic ss t in
      (* Desugaring of arguments and computation of argument impliciteness. *)
      let (ao, impl) =
        match ao with
        | None    -> (None, List.map (fun (_,_,impl) -> impl) xs)
        | Some(a) ->
            let a = if xs = [] then a else Pos.none (P_Prod(xs,a)) in
            (Some(a), Scope.get_implicitness a)
      in
      let ao = Option.map (scope_basic ss) ao in
      (* If a type [a] is given, then we check that [a] is typable by a sort
         and that [t] has type [a]. Otherwise, we try to infer the type of
         [t] and return it. *)
      let a =
        match ao with
        | Some(a) ->
            Typing.sort_type ss.builtins Ctxt.empty a;
            if Typing.check ss.builtins Ctxt.empty t a then a else
            fatal cmd.pos "Term [%a] does not have type [%a]." pp t pp a
        | None    ->
            match Typing.infer ss.builtins Ctxt.empty t with
            | Some(a) -> a
            | None    -> fatal cmd.pos "Cannot infer the type of [%a]." pp t
      in
      (* We check that no metavariable remains. *)
      if Basics.has_metas t || Basics.has_metas a then
        begin
          fatal_msg "The definition of [%s] or its type \
                     have unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a ≔ %a." x.elt pp t pp a
        end;
      (* Actually add the symbol to the signature. *)
      let s = Sign.add_symbol ss.signature Defin x a impl in
      out 3 "(symb) %s (definition).\n" s.sym_name;
      (* Also add its definition, if it is not opaque. *)
      if not op then s.sym_def := Some(t);
      ({ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}, None)
  | P_theorem(stmt, ts, pe)    ->
      let (x,xs,a) = stmt.elt in
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments of [a]. *)
      let a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
      (* Obtaining the implicitness of arguments. *)
      let impl = Scope.get_implicitness a in
      (* Scoping the type (statement) of the theorem. *)
      let a = scope_basic ss a in
      (* Check that [a] is typable and that its type is a sort. *)
      Typing.sort_type ss.builtins Ctxt.empty a;
      (* We check that no metavariable remains in [a]. *)
      if Basics.has_metas a then
        begin
          fatal_msg "The type of [%s] has unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a." x.elt pp a
        end;
      (* Initialize proof state. *)
      let st = Proof.init ss.builtins x a in
      (* Build proof checking data. *)
      let finalize ss st =
        match pe.elt with
        | P_proof_abort ->
            (* Just ignore the command, with a warning. *)
            wrn cmd.pos "Proof aborted."; ss
        | P_proof_admit ->
            (* If the proof is finished, display a warning. *)
            if Proof.finished st then
              wrn cmd.pos "The proof is finished. You can use 'qed' instead.";
            (* Add a symbol corresponding to the proof, with a warning. *)
            let s = Sign.add_symbol ss.signature Const x a impl in
            out 3 "(symb) %s (admit).\n" s.sym_name;
            wrn cmd.pos "Proof admitted.";
            {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
        | P_proof_qed   ->
            (* Check that the proof is indeed finished. *)
            if not (Proof.finished st) then
              begin
                let _ = Tactics.handle_tactic ss st (none P_tac_print) in
                fatal cmd.pos "The proof is not finished."
              end;
            (* Add a symbol corresponding to the proof. *)
            let s = Sign.add_symbol ss.signature Const x a impl in
            out 3 "(symb) %s (qed).\n" s.sym_name;
            {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
      in
      let data =
        { pdata_stmt_pos = stmt.pos ; pdata_p_state = st ; pdata_tactics = ts
        ; pdata_finalize = finalize ; pdata_term_pos = pe.pos }
      in
      (ss, Some(data))
  | P_assert(must_fail, asrt)  ->
      let result =
        match asrt with
        | P_assert_typing(t,a) ->
            let t = scope_basic ss t in
            let a = scope_basic ss a in
            Typing.sort_type ss.builtins Ctxt.empty a;
            (try Typing.check ss.builtins Ctxt.empty t a with _ -> false)
        | P_assert_conv(a,b)   ->
            let t = scope_basic ss a in
            let u = scope_basic ss b in
            match (Typing.infer ss.builtins Ctxt.empty t,
                   Typing.infer ss.builtins Ctxt.empty u) with
            | (Some(a), Some(b)) ->
                if Eval.eq_modulo a b then Eval.eq_modulo t u else
                fatal cmd.pos "Infered types not convertible (in assertion)."
            | (None   , _      ) ->
                fatal a.pos "Type cannot be infered (in assertion)."
            | (_      , None   ) ->
                fatal b.pos "Type cannot be infered (in assertion)."
      in
      if result = must_fail then fatal cmd.pos "Assertion failed."; (ss, None)
  | P_set(cfg)                 ->
      let ss =
        match cfg with
        | P_config_debug(e,s)     ->
            (* Just update the option, state not modified. *)
            Console.set_debug e s; ss
        | P_config_verbose(i)     ->
            (* Just update the option, state not modified. *)
            Console.verbose := i; ss
        | P_config_flag(id,b)     ->
            (* We set the value of the flag, if it exists. *)
            begin
              try Console.set_flag id b with Not_found ->
                wrn cmd.pos "Unknown flag \"%s\"." id
            end; ss
        | P_config_builtin(s,qid) ->
            (* Set the builtin symbol [s]. *)
            let builtins = !(ss.signature.sign_builtins) in
            if StrMap.mem s builtins then
              fatal cmd.pos "Builtin [%s] already exists." s;
            let sym, _ = find_sym false ss qid in
            check_builtin_nat cmd.pos builtins s sym;
            Rewrite.check_builtin cmd.pos builtins s sym;
            Sign.add_builtin ss.signature s sym;
            {ss with builtins = StrMap.add s sym ss.builtins}
        | P_config_binop(binop)   ->
            let (s, _, _, qid) = binop in
            (* Define the binary operator [s]. *)
            let sym, _ = find_sym false ss qid in
            Sign.add_binop ss.signature s (sym, binop); ss
      in
      (ss, None)
  | P_infer(t, cfg)            ->
      (* Infer the type of [t]. *)
      let t_pos = t.pos in
      let t = scope_basic ss t in
      let a =
        match Typing.infer ss.builtins Ctxt.empty t with
        | Some(a) -> Eval.eval cfg a
        | None    -> fatal t_pos "Cannot infer the type of [%a]." pp t
      in
      out 3 "(infr) %a : %a\n" pp t pp a; (ss, None)
  | P_normalize(t, cfg)        ->
      (* Infer a type for [t], and evaluate [t]. *)
      let t_pos = t.pos in
      let t = scope_basic ss t in
      let v =
        match Typing.infer ss.builtins Ctxt.empty t with
        | Some(_) -> Eval.eval cfg t
        | None    -> fatal t_pos "Cannot infer the type of [%a]." pp t
      in
      out 3 "(eval) %a\n" pp v; (ss, None)

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Pervasives.ref infinity

(** [handle_cmd ss cmd] is similar to [handle_cmd_aux ss cmd] but it adds some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle_cmd : sig_state -> command -> sig_state * proof_data option =
    fun ss cmd ->
  try
    let (tm, ss) = time (handle_cmd_aux ss) cmd in
    if Pervasives.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           ->
      fatal cmd.pos "Uncaught exception [%s]." (Printexc.to_string e)
