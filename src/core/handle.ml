(** Toplevel commands. *)

open! Lplib
open Lplib.Extra

open Timed
open Console
open Terms
open Sign
open Pos
open Files
open Syntax
open P_terms
open Sig_state
open Scope
open Print

(** Logging function for command handling. *)
let log_hndl = new_logger 'h' "hndl" "command handling"
let log_hndl = log_hndl.logger

(* Register a check for the type of the builtin symbols "0" and "+1". *)
let _ =
  let register = Builtin.register_expected_type (Unif.eq []) pp_term in
  let expected_zero_type ss _pos =
    try
      match !((StrMap.find "+1" ss.builtins).sym_type) with
      | Prod(a,_) -> a
      | _ -> assert false
    with Not_found -> Meta (Meta.fresh Type 0, [||])
  in
  register "0" expected_zero_type;
  let expected_succ_type ss _pos =
    let typ_0 =
      try lift !((StrMap.find "0" ss.builtins).sym_type)
      with Not_found -> _Meta (Meta.fresh Type 0) [||]
    in
    Bindlib.unbox (_Impl typ_0 typ_0)
  in
  register "+1" expected_succ_type

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

(** [handle_modifiers ms] verifies that the modifiers in [ms] are compatible.
    If so, they are returned as a tuple, otherwise, the incompatible modifiers
    are returned. *)
let handle_modifiers : p_modifier loc list -> (prop * expo * match_strat) =
  fun ms ->
  let is_expo {elt; _} = match elt with P_expo(_) -> true | _ -> false in
  let is_prop {elt; _} = match elt with P_prop(_) -> true | _ -> false in
  let is_mstrat {elt; _} = match elt with P_mstrat(_) -> true | _ -> false in
  let die (mods: p_modifier loc list) =
    let pp_sep oc () = Format.pp_print_string oc "; " in
    let pp_pmloc oc (m: p_modifier loc) =
      Format.fprintf oc "%a:\"%a\"" Pos.print_short m.pos Pretty.pp_modifier m
    in
    fatal_no_pos "%a" (Format.pp_print_list ~pp_sep pp_pmloc) mods
  in
  let prop = List.filter is_prop ms in
  let prop =
    match prop with
    | _::_::_ ->
        fatal_msg "Only one property modifier can be used, \
                   %d have been found: " (List.length prop);
        die prop
    | [{elt=P_prop(p); _}] -> p
    | [] -> Defin
    | _ -> assert false
  in
  let expo = List.filter is_expo ms in
  let expo =
    match expo with
    | _::_::_ ->
        fatal_msg "Only one exposition marker can be used, \
                   %d have been found: " (List.length expo);
        die expo
    | [{elt=P_expo(e); _}] -> e
    | [] -> Public
    | _ -> assert false
  in
  let mstrat = List.filter is_mstrat ms in
  let mstrat =
    match mstrat with
    | _::_::_ ->
        fatal_msg "Only one strategy modifier can be used, \
                   %d have been found: " (List.length mstrat);
        die mstrat
    | [{elt=P_mstrat(s); _ }] -> s
    | [] -> Eager
    | _ -> assert false
  in
  (prop, expo, mstrat)

(** [handle_require_as pos ss p id] handles the command [require p as id] with
    [ss] as the signature state. On success, an updated signature state is
    returned. *)
let handle_require_as : popt -> sig_state -> Path.t -> ident -> sig_state =
    fun pos ss p id ->
  let ss = handle_require false pos ss p in
  let aliases = StrMap.add id.elt p ss.aliases in
  let path_map = PathMap.add p id.elt ss.path_map in
  {ss with aliases; path_map}

(** [handle_symbol ss e p strat x xs a] handles the command
    [e p strat symbol x xs : a] with [ss] as the signature state.
    On success, an updated signature state and the new symbol are returned. *)
let handle_symbol :
  sig_state -> expo -> prop -> match_strat -> ident -> p_arg list ->
  p_type -> sig_state * sym = fun ss e p strat x xs a ->
  let scope_basic exp = Scope.scope_term exp ss Env.empty in
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
  Typing.sort_type [] a;
  (* We check that no metavariable remains. *)
  if Basics.has_metas true a then
    begin
      fatal_msg "The type of [%s] has unsolved metavariables.\n" x.elt;
      fatal x.pos "We have %s : %a." x.elt pp_term a
    end;
  (* Actually add the symbol to the signature and the state. *)
  out 3 "(symb) %s : %a\n" x.elt pp_term a;
  Sig_state.add_symbol ss e p strat x a impl None

(** [handle_rule ss syms r] checks rule [r], adds it in [ss] and returns the
   set [syms] extended with the symbol [s] defined by [r]. However, it does
   not update the decision tree of [s]. *)
let handle_rule : sig_state -> p_rule -> sym = fun ss r ->
  let pr = scope_rule false ss r in
  let sym = pr.elt.pr_sym in
  if !(sym.sym_def) <> None then
    fatal pr.pos "Rewriting rules cannot be given for defined symbol [%s]."
      sym.sym_name;
  let rule = Sr.check_rule pr in
  Sign.add_rule ss.signature sym rule;
  out 3 "(rule) %a\n" pp_rule (sym, rule);
  sym

(** [handle_rules ss rs] handles the rules [rs] in signature state [ss], and
   update the decision trees of the symboles defined by [rs]. *)
let handle_rules : sig_state -> p_rule list -> sig_state = fun ss rs ->
  let handle_rule syms r = SymSet.add (handle_rule ss r) syms in
  let syms = List.fold_left handle_rule SymSet.empty rs in
  SymSet.iter Tree.update_dtree syms;
  ss

(** [handle_cmd ss cmd] tries to handle the command [cmd] with [ss] as the
    signature state. On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
let handle_cmd : sig_state -> p_command -> sig_state * proof_data option =
  fun ss cmd ->
  let scope_basic exp = Scope.scope_term exp ss Env.empty in
  match cmd.elt with
  | P_require(b,ps)              ->
      let ps = List.map (List.map fst) ps in
      (List.fold_left (handle_require b cmd.pos) ss ps, None)
  | P_require_as(p,id)           ->
      let id = Pos.make id.pos (fst id.elt) in
      (handle_require_as cmd.pos ss (List.map fst p) id, None)
  | P_open(ps)                   ->
      let ps = List.map (List.map fst) ps in
      (List.fold_left (handle_open cmd.pos) ss ps, None)
  | P_symbol(ms, x, xs, a)     ->
      (* Verify the modifiers. *)
      let (prop, expo, mstrat) = handle_modifiers ms in
      (fst (handle_symbol ss expo prop mstrat x xs a), None)
  | P_rules(rs)                  ->
      let handle_rule syms r = SymSet.add (handle_rule ss r) syms in
      let syms = List.fold_left handle_rule SymSet.empty rs in
      SymSet.iter Tree.update_dtree syms;
      (ss, None)
  | P_definition(ms, op, x, xs, ao, t) ->
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Verify modifiers. *)
      let (prop, expo, mstrat) = handle_modifiers ms in
      if prop = Const then
        fatal cmd.pos "A definition cannot be a constant.";
      if mstrat <> Eager then
        fatal cmd.pos "Pattern matching strategy modifiers cannot be used \
                       in definitions.";
      (* Desugaring of arguments and scoping of [t]. *)
      let t = if xs = [] then t else Pos.none (P_Abst(xs, t)) in
      let t = scope_basic expo t in
      (* Desugaring of arguments and computation of argument impliciteness. *)
      let (ao, impl) =
        match ao with
        | None    -> (None, List.map (fun (_,_,impl) -> impl) xs)
        | Some(a) ->
            let a = if xs = [] then a else Pos.none (P_Prod(xs,a)) in
            (Some(a), Scope.get_implicitness a)
      in
      let ao = Option.map (scope_basic expo) ao in
      (* If a type [a] is given, then we check that [a] is typable by a sort
         and that [t] has type [a]. Otherwise, we try to infer the type of
         [t] and return it. *)
      let a =
        match ao with
        | Some(a) ->
            Typing.sort_type [] a;
            if Typing.check [] t a then a else
              fatal cmd.pos "The term [%a] does not have type [%a]."
                pp_term t pp_term a
        | None    ->
            match Typing.infer [] t with
            | Some(a) -> a
            | None    ->
                fatal cmd.pos "Cannot infer the type of [%a]." pp_term t
      in
      (* We check that no metavariable remains. *)
      if Basics.has_metas true t || Basics.has_metas true a then
        begin
          fatal_msg "The definition of [%s] or its type \
                     have unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a ≔ %a." x.elt pp_term a pp_term t
        end;
      (* Actually add the symbol to the signature. *)
      out 3 "(symb) %s ≔ %a\n" x.elt pp_term t;
      let d = if op then None else Some(t) in
      (fst (Sig_state.add_symbol ss expo Defin Eager x a impl d), None)
  | P_inductive(ms, p_ind_list)     ->
      (* Check modifiers. *)
      let (prop, e, mstrat) = handle_modifiers ms in
      if prop <> Defin then
        fatal cmd.pos "Property modifiers cannot be used on inductive types.";
      if mstrat <> Eager then
        fatal cmd.pos "Pattern matching strategy modifiers cannot be used on \
                       inductive types.";
      (* Add inductive types in the signature. *)
      let add_ind_sym (ss, ind_sym_list) p_ind =
        let (id, pt, _) = p_ind.elt in
        let (ss, ind_sym) = handle_symbol ss e Injec Eager id [] pt in
        (ss, ind_sym::ind_sym_list)
      in
      let (ss, ind_sym_list_rev) =
        List.fold_left add_ind_sym (ss, []) p_ind_list in
      (* Add constructors in the signature. *)
      let add_constructors (ss, cons_sym_list_list) p_ind =
        let (_, _, p_cons_list) = p_ind.elt in
        let add_cons_sym (ss, cons_sym_list) (id, pt) =
          let (ss, cons_sym) = handle_symbol ss e Const Eager id [] pt in
          (ss, cons_sym::cons_sym_list)
        in
        let (ss, cons_sym_list_rev) =
          List.fold_left add_cons_sym (ss, []) p_cons_list in
        (* Reverse the list of constructors previously computed to preserve
           the initial order. *)
        let cons_sym_list = List.rev cons_sym_list_rev in
        (ss, cons_sym_list::cons_sym_list_list)
      in
      let (ss, cons_sym_list_list_rev) =
        List.fold_left add_constructors (ss, []) p_ind_list
      in
      let ind_list =
        List.fold_left2 (fun acc x y -> (x,y)::acc) []
          ind_sym_list_rev cons_sym_list_list_rev
      in
      (* Compute data useful for generating the induction principles. *)
      let c = Inductive.get_config ss cmd.pos in
      let p_str, x_str = Inductive.gen_safe_prefixes ind_list in
      let ind_pred_map =
        Inductive.create_ind_pred_map cmd.pos c ind_list p_str x_str
      in
      (* Compute the induction principles. *)
      let rec_typ_list_rev =
        Inductive.gen_rec_types c ss cmd.pos ind_list ind_pred_map x_str
      in
      (* Add the induction principles in the signature. *)
      let add_recursor (ss, rec_sym_list) ind_sym rec_typ =
        let rec_name = Inductive.rec_name ind_sym in
        if Sign.mem ss.signature rec_name then
          fatal cmd.pos "Symbol [%s] already exists." rec_name;
        (* If [ind_sym] is a declared identifier, then [rec_sym] must be
           declared too. *)
        if StrSet.mem ind_sym.sym_name !(ss.signature.sign_idents) then
          Sign.add_ident ss.signature rec_name;
        let (ss, rec_sym) =
          out 3 "(symb) %s : %a\n" rec_name pp_term rec_typ;
          let rec_name = Pos.make cmd.pos rec_name in
          Sig_state.add_symbol ss e Defin Eager rec_name rec_typ [] None
        in
        (ss, rec_sym::rec_sym_list)
      in
      let (ss, rec_sym_list) =
        List.fold_left2 add_recursor (ss, [])
          ind_sym_list_rev rec_typ_list_rev
      in
      (* Add recursor rules in the signature. *)
      with_no_wrn
        (Inductive.iter_rec_rules cmd.pos ind_list ind_pred_map)
        (fun r -> ignore (handle_rule ss r));
      List.iter Tree.update_dtree rec_sym_list;
      (* Store the inductive structure in the signature *)
      List.iter2
        (fun (ind_sym, cons_sym_list) rec_sym ->
          Sign.add_inductive ss.signature ind_sym cons_sym_list rec_sym)
        ind_list
        rec_sym_list;
      (ss, None)
  | P_theorem(ms, stmt, ts, pe) ->
      let (x,xs,a) = stmt.elt in
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Desugaring of arguments of [a]. *)
      let a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
      (* Obtaining the implicitness of arguments. *)
      let impl = Scope.get_implicitness a in
      (* Verify modifiers. *)
      let (prop, expo, mstrat) = handle_modifiers ms in
      if prop <> Defin then
        fatal cmd.pos "Property modifiers cannot be used in theorems.";
      if mstrat <> Eager then
        fatal cmd.pos "Pattern matching strategy modifiers cannot be used \
                       in theorems.";
      (* Scoping the type (statement) of the theorem. *)
      let a = scope_basic expo a in
      (* Check that [a] is typable and that its type is a sort. *)
      Typing.sort_type [] a;
      (* We check that no metavariable remains in [a]. *)
      if Basics.has_metas true a then
        begin
          fatal_msg "The type of [%s] has unsolved metavariables.\n" x.elt;
          fatal x.pos "We have %s : %a." x.elt pp_term a
        end;
      (* Initialize proof state and save configuration data. *)
      let st = Proof.init x a in
      Console.State.push ();
      (* Build proof checking data. *)
      let finalize ss st =
        Console.State.pop ();
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
            fst (Sig_state.add_symbol ss expo Const Eager x a impl None)
        | P_proof_qed   ->
            (* Check that the proof is indeed finished. *)
            if not (Proof.finished st) then
              begin
                let _ = Tactics.handle_tactic ss st (none P_tac_print) in
                fatal cmd.pos "The proof is not finished."
              end;
            (* Add a symbol corresponding to the proof. *)
            out 3 "(symb) %s (qed)\n" x.elt;
            fst (Sig_state.add_symbol ss expo Const Eager x a impl None)
      in
      let data =
        { pdata_stmt_pos = stmt.pos ; pdata_p_state = st ; pdata_tactics = ts
          ; pdata_finalize = finalize ; pdata_term_pos = pe.pos }
      in
      (ss, Some(data))
  | P_set(cfg)                 ->
      let ss =
        let with_path : Path.t -> qident -> qident = fun path qid ->
          let path = List.map (fun s -> (s, false)) path in
          Pos.make qid.pos (path, snd qid.elt)
        in
        match cfg with
        | P_config_builtin(s,qid) ->
            (* Set the builtin symbol [s]. *)
            if StrMap.mem s ss.builtins then
              fatal cmd.pos "Builtin [%s] already exists." s;
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            Builtin.check ss cmd.pos s sym;
            out 3 "(conf) set builtin \"%s\" ≔ %a\n" s pp_symbol sym;
            Sig_state.add_builtin ss s sym
        | P_config_unop(unop)     ->
            let (s, prio, qid) = unop in
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            (* Make sure the operator has a fully qualified [qid]. *)
            let unop = (s, prio, with_path sym.sym_path qid) in
            out 3 "(conf) %a %a\n" pp_symbol sym pp_hint (Prefix unop);
            Sig_state.add_unop ss s (sym, unop)
        | P_config_binop(binop)   ->
            let (s, assoc, prio, qid) = binop in
            (* Define the binary operator [sym]. *)
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            (* Make sure the operator has a fully qualified [qid]. *)
            let binop = (s, assoc, prio, with_path sym.sym_path qid) in
            out 3 "(conf) %a %a\n" pp_symbol sym pp_hint (Infix binop);
            Sig_state.add_binop ss s (sym, binop);
        | P_config_ident(id)      ->
            Sign.add_ident ss.signature id;
            out 3 "(conf) declared identifier \"%s\"\n" id; ss
        | P_config_quant(qid)     ->
            let sym = find_sym ~prt:true ~prv:true false ss qid in
            out 3 "(conf) %a quantifier\n" pp_symbol sym;
            Sig_state.add_quant ss sym
        | P_config_unif_rule(h)   ->
            (* Approximately same processing as rules without SR checking. *)
            let pur = (scope_rule true ss h).elt in
            let urule =
              { lhs = pur.pr_lhs
              ; rhs = Bindlib.(unbox (bind_mvar pur.pr_vars pur.pr_rhs))
              ; arity = List.length pur.pr_lhs
              ; arities = pur.pr_arities
              ; vars = pur.pr_vars
              ; xvars_nb = pur.pr_xvars_nb }
            in
            Sign.add_rule ss.signature Unif_rule.equiv urule;
            Tree.update_dtree Unif_rule.equiv;
            out 3 "(hint) [%a]\n" Print.pp_rule (Unif_rule.equiv, urule); ss
      in
      (ss, None)
  | P_query(q)                 ->
      Queries.handle_query ss None q; (ss, None)

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Stdlib.ref infinity

(** [handle_cmd ss cmd] adds to the previous [handle_cmd] some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle_cmd : sig_state -> p_command -> sig_state * proof_data option =
  fun ss cmd ->
  Print.sig_state := ss;
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
