(** Toplevel commands. *)

open! Lplib
open Lplib.Extra
open Timed
open Common
open Error
open Core
open Term
open Sign
open Pos
open Parsing
open Syntax
open Tags
open Sig_state
open Scope
open Print
open Proof
open Debug

(** Logging function for command handling. *)
let log_hndl = new_logger 'h' "hndl" "command handling"
let log_hndl = log_hndl.logger

(* Register a check for the type of the builtin symbols "0" and "+1". *)
let _ =
  let register = Builtin.register_expected_type (Unif.eq_noexn []) pp_term in
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

(** [handle_open ss p] handles the command [open p] with [ss] as the
   signature state. On success, an updated signature state is returned. *)
let handle_open : sig_state -> p_path -> sig_state =
  fun ss {elt=p;pos} ->
  (* Obtain the signature corresponding to [m]. *)
  let sign =
    try Path.Map.find p !(Sign.loaded) with Not_found ->
      (* The signature has not been required... *)
      fatal pos "Module %a has not been required." pp_path p
  in
  (* Open the module. *)
  open_sign ss sign

(** [handle_require b ss p] handles the command [require p] (or [require
   open p] if b is true) with [ss] as the signature state and [compile] the
   main compile function (passed as argument to avoid cyclic dependencies).
   On success, an updated signature state is returned. *)
let handle_require :
      (Path.t -> Sign.t) -> bool -> sig_state -> p_path -> sig_state =
  fun compile b ss ({elt=p;pos} as mp) ->
  (* Check that the module has not already been required. *)
  if Path.Map.mem p !(ss.signature.sign_deps) then
    fatal pos "Module %a is already required." pp_path p;
  (* Compile required path (adds it to [Sign.loaded] among other things) *)
  ignore (compile p);
  (* Add the dependency (it was compiled already while parsing). *)
  ss.signature.sign_deps := Path.Map.add p [] !(ss.signature.sign_deps);
  if b then handle_open ss mp else ss

(** [handle_require_as compile ss p id] handles the command
    [require p as id] with [ss] as the signature state and [compile] the main
    compilation function passed as argument to avoid cyclic dependencies. On
    success, an updated signature state is returned. *)
let handle_require_as :
    (Path.t -> Sign.t) -> sig_state -> p_path -> p_ident -> sig_state =
  fun compile ss ({elt=p;_} as mp) {elt=id;_} ->
  let ss = handle_require compile false ss mp in
  let alias_path = StrMap.add id p ss.alias_path in
  let path_alias = Path.Map.add p id ss.path_alias in
  {ss with alias_path; path_alias}

(** [handle_modifiers ms] verifies that the modifiers in [ms] are compatible.
    If so, they are returned as a tuple. Otherwise, it fails. *)
let handle_modifiers : p_modifier list -> (prop * expo * match_strat) =
  fun ms ->
  let die (ms: p_modifier list) =
    let modifier oc (m: p_modifier) =
      Format.fprintf oc "%a:\"%a\"" Pos.pp_short m.pos Pretty.modifier m
    in
    fatal_no_pos "%a" (List.pp modifier "; ") ms
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

(** [handle_rule ss syms r] checks rule [r], adds it in [ss] and returns the
   set [syms] extended with the symbol [s] defined by [r]. However, it does
   not update the decision tree of [s]. *)
let handle_rule : sig_state -> p_rule -> sym = fun ss r ->
  if !log_enabled then log_hndl "%a" (Pretty.rule "rule") r;
  let pr = scope_rule false ss r in
  let sym = pr.elt.pr_sym in
  if !(sym.sym_def) <> None then
    fatal pr.pos "No rewriting rule can be given on the defined symbol %a."
      pp_sym sym;
  let rule = Tool.Sr.check_rule pr in
  Sign.add_rule ss.signature sym rule;
  Console.out 3 (red "(rule) add %a\n") pp_rule (sym, rule);
  sym

(** [handle_rules ss rs] handles the rules [rs] in signature state [ss], and
   update the decision trees of the symboles defined by [rs]. *)
let handle_rules : sig_state -> p_rule list -> sig_state = fun ss rs ->
  let handle_rule syms r = SymSet.add (handle_rule ss r) syms in
  let syms = List.fold_left handle_rule SymSet.empty rs in
  SymSet.iter Tree.update_dtree syms;
  ss

(** [handle_inductive_symbol ss e p strat x xs a] handles the command
    [e p strat symbol x xs : a] with [ss] as the signature state.
    On success, an updated signature state and the new symbol are returned. *)
let handle_inductive_symbol : sig_state -> expo -> prop -> match_strat
    -> p_ident -> p_params list -> p_term -> sig_state * sym =
  fun ss expo prop mstrat ({elt=name;pos} as id) xs typ ->
  (* We check that [id] is not already used. *)
  if Sign.mem ss.signature name then
    fatal pos "Symbol %a already exists." pp_uid name;
  (* Desugaring of arguments of [typ]. *)
  let typ = if xs = [] then typ else Pos.none (P_Prod(xs, typ)) in
  (* Obtaining the implicitness of arguments. *)
  let impl = Scope.get_implicitness typ in
  (* We scope the type of the declaration. *)
  let typ = Scope.scope_term expo ss Env.empty IntMap.empty typ in
  (* We check that [a] is typable by a sort. *)
  Infer.check_sort Unif.solve_noexn pos [] typ;
  (* We check that no metavariable remains. *)
  if LibTerm.Meta.has true typ then
    (fatal_msg "The type of %a has unsolved metavariables.\n" pp_uid name;
     fatal pos "We have %a : %a." pp_uid name pp_term typ);
  (* Actually add the symbol to the signature and the state. *)
  Console.out 3 (red "(symb) %a : %a\n") pp_uid name pp_term typ;
  Sig_state.add_symbol ss expo prop mstrat false id typ impl None

(** Representation of a yet unchecked proof. The structure is initialized when
    the proof mode is entered, and its finalizer is called when the proof mode
    is exited (i.e., when a terminator like “end” is used).  Note that tactics
    do not work on this structure directly,  although they act on the contents
    of its [pdata_p_state] field. *)
type proof_data =
  { pdata_stmt_pos : Pos.popt (** Position of the declared symbol. *)
  ; pdata_p_state  : proof_state (** Proof state. *)
  ; pdata_tactics  : p_tactic list (** Tactics. *)
  ; pdata_finalize : sig_state -> proof_state -> sig_state (** Finalizer. *)
  ; pdata_end_pos  : Pos.popt (** Position of the proof's terminator. *)
  ; pdata_expo     : expo (** Allowed exposition of symbols in the proof
                                   script. *) }

(** Number of admitted axioms in the current signature. Used to name the
    generated axioms. This reference is reset in {!module:Compile} for each
    new compiled module. *)
let admitted : int Stdlib.ref = Stdlib.ref (-1)

(** [handle compile ss cmd] tries to handle the command [cmd] with [ss] as
    the signature state and [compile] as the main compilation function
    processing lambdapi modules (it is passed as argument to avoid cyclic
    dependencies). On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
let handle : (Path.t -> Sign.t) -> sig_state -> p_command ->
    sig_state * proof_data option * Query.result =
  fun compile ss ({elt; pos} as cmd) ->
  if !log_enabled then
    log_hndl (blu "%f %a\n%a") (Sys.time()) Pos.pp pos Pretty.command cmd;
  let scope expo = Scope.scope_term expo ss Env.empty IntMap.empty in
  match elt with
  | P_query(q) -> (ss, None, Query.handle ss None q)
  | P_require(b,ps) ->
      (List.fold_left (handle_require compile b) ss ps, None, None)
  | P_require_as(p,id) -> (handle_require_as compile ss p id, None, None)
  | P_open(ps) -> (List.fold_left handle_open ss ps, None, None)
  | P_rules(rs) ->
      let handle_rule syms r = SymSet.add (handle_rule ss r) syms in
      let syms = List.fold_left handle_rule SymSet.empty rs in
      SymSet.iter Tree.update_dtree syms;
      (ss, None, None)
  | P_builtin(s,qid) ->
      let sym = find_sym ~prt:true ~prv:true ss qid in
      Builtin.check ss pos s sym;
      Console.out 3 "(conf) set builtin \"%s\" ≔ %a\n" s pp_sym sym;
      (add_builtin ss s sym, None, None)
  | P_notation(qid,n) ->
      let sym = find_sym ~prt:true ~prv:true ss qid in
      Console.out 3 "(conf) %a %a\n" pp_sym sym pp_notation n;
      (add_notation ss sym n, None, None)
  | P_unif_rule(h) ->
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
      Console.out 3 "(hint) %a\n" pp_unif_rule (Unif_rule.equiv, urule);
      (ss, None, None)

  | P_inductive(ms, params, p_ind_list) ->
      (* Check modifiers. *)
      let (prop, expo, mstrat) = handle_modifiers ms in
      if prop <> Defin then
        fatal pos "Property modifiers cannot be used on inductive types.";
      if mstrat <> Eager then
        fatal pos "Pattern matching strategy modifiers cannot be used on \
                       inductive types.";
      (* Add inductive types in the signature. *)
      let add_ind_sym (ss, ind_sym_list) {elt=(id,pt,_); _} =
        let (ss, ind_sym) =
          handle_inductive_symbol ss expo Const Eager id params pt in
        (ss, ind_sym::ind_sym_list)
      in
      let (ss, ind_sym_list_rev) =
        List.fold_left add_ind_sym (ss, []) p_ind_list in
      (* Set parameters as implicit in the type of constructors. *)
      let params =
        List.map (fun (idopts,typopt,_) -> (idopts,typopt,true)) params in
      (* Add constructors in the signature. *)
      let add_constructors
            (ss, cons_sym_list_list) {elt=(_,_,p_cons_list); _} =
        let add_cons_sym (ss, cons_sym_list) (id, pt) =
          let (ss, cons_sym) =
            handle_inductive_symbol ss expo Const Eager id params pt in
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
        List.fold_left2
          (fun acc ind_sym cons_sym_list -> (ind_sym,cons_sym_list)::acc)
          []
          ind_sym_list_rev cons_sym_list_list_rev
      in
      (* Compute data useful for generating the induction principles. *)
      let cfg = Inductive.get_config ss pos in
      let a_str, p_str, x_str = Inductive.gen_safe_prefixes ind_list in
      let ind_nb_params = List.length params in
      let vs, env, ind_pred_map =
        Inductive.create_ind_pred_map pos cfg ind_nb_params ind_list
          a_str p_str x_str
      in
      (* Compute the induction principles. *)
      let rec_typ_list_rev =
        Inductive.gen_rec_types cfg pos ind_list vs env ind_pred_map x_str
      in
      (* Add the induction principles in the signature. *)
      let add_recursor (ss, rec_sym_list) ind_sym rec_typ =
        let rec_name = Inductive.rec_name ind_sym in
        if Sign.mem ss.signature rec_name then
          fatal pos "Symbol %a already exists." pp_uid rec_name;
        let (ss, rec_sym) =
          Console.out 3 (red "(symb) %a : %a\n")
            pp_uid rec_name pp_term rec_typ;
          let id = Pos.make pos rec_name in
          Sig_state.add_symbol ss expo Defin Eager false id rec_typ [] None
        in
        (ss, rec_sym::rec_sym_list)
      in
      let (ss, rec_sym_list) =
        List.fold_left2 add_recursor (ss, [])
          ind_sym_list_rev rec_typ_list_rev
      in
      (* Add recursor rules in the signature. *)
      with_no_wrn
        (Inductive.iter_rec_rules pos ind_list vs ind_pred_map)
        (fun r -> ignore (handle_rule ss r));
      List.iter Tree.update_dtree rec_sym_list;
      (* Store the inductive structure in the signature *)
      let ind_nb_types = List.length ind_list in
      List.iter2
        (fun (ind_sym, cons_sym_list) rec_sym ->
          Sign.add_inductive ss.signature ind_sym cons_sym_list rec_sym
            ind_nb_params ind_nb_types)
        ind_list
        rec_sym_list;
      (ss, None, None)

  | P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf;
              p_sym_def} ->
    (* Check that this is a syntactically valid symbol declaration. *)
    begin
      match (p_sym_typ, p_sym_def, p_sym_trm, p_sym_prf) with
      | (None, true, None, Some _) -> fatal pos "missing type"
      | (   _, true, None, None  ) -> fatal pos "missing definition"
      | _ -> ()
    end;
    (* We check that the identifier is not already used. *)
    let {elt=id; _} = p_sym_nam in
    if Sign.mem ss.signature id then
      fatal p_sym_nam.pos "Symbol %a already exists." pp_uid id;
    (* Verify modifiers. *)
    let (prop, expo, mstrat) = handle_modifiers p_sym_mod in
    let opaq = List.exists Syntax.is_opaq p_sym_mod in
    let pdata_expo = if p_sym_def && opaq then Privat else expo in
    (match p_sym_def, opaq, prop, mstrat with
     | false, true, _, _ ->
         fatal pos "Symbol declarations cannot be opaque."
     | true, _, Const, _ ->
         fatal pos "Definitions cannot be constant."
     | true, _, _, Sequen ->
         fatal pos "Definitions cannot have matching strategies."
     | _, _, _, _ -> ());
    (* Build proof data. *)
    let data =
      (* Desugaring of arguments and scoping of [p_sym_trm]. *)
      let pt, t =
        match p_sym_trm with
        | Some pt ->
            let pt =
              if p_sym_arg = [] then pt
              else let pos = Pos.(cat (end_pos p_sym_nam.pos) pt.pos) in
                   Pos.make pos (P_Abst(p_sym_arg, pt))
            in
            Some pt, Some (scope expo pt)
        | None -> None, None
      in
      (* Argument impliciteness. *)
      let ao, impl =
        match p_sym_typ with
        | None    -> (None, List.map (fun (_,_,impl) -> impl) p_sym_arg)
        | Some(a) ->
            let a =
              if p_sym_arg = [] then a
              else Pos.make p_sym_nam.pos (P_Prod(p_sym_arg,a))
            in
            (Some(a), Scope.get_implicitness a)
      in
      (* Scope the type and get its metavariables. *)
      let ao, metas_a =
        match ao with
        | Some a -> let a = scope expo a in Some a, LibTerm.Meta.get true a
        | None -> None, MetaSet.empty
      in
      (* Get the type of the symbol and the goals to solve for the declaration
         to be well-typed. *)
      let proof_goals, a = goals_of_typ pos ao t in
      (* Add the metas of [a] as goals. *)
      let proof_goals = add_goals_of_metas metas_a proof_goals in
      (* Add the definition as goal so that we can refine on it. *)
      let proof_term =
        if p_sym_def then Some (Meta.fresh ~name:id a 0) else None in
      (* Get tactics and proof end. *)
      let ts, pe =
        match p_sym_prf with
        | None -> [], Pos.make (Pos.end_pos pos) P_proof_end
        | Some (ts, pe) -> ts, pe
      in
      (* Initialize proof state. *)
      Console.State.push ();
      (* Build finalizer. *)
      let finalize ss ps =
        Console.State.pop ();
        match pe.elt with
        | P_proof_abort ->
            (* Just ignore the command with a warning. *)
            wrn pe.pos "Proof aborted."; ss
        | _ ->
            match pe.elt with
            | P_proof_abort -> assert false (* Handled above *)
            | P_proof_admit ->
                (* If the proof is finished, display a warning. *)
                if finished ps then
                  wrn pe.pos "The proof is finished. Use 'end' instead.";
                (* [add_axiom ss m] adds an axiom for meta [m] in signature
                   state [ss]. *)
                let add_axiom ss m =
                  let name =
                    let m_name =
                      match m.meta_name with Some n -> "_" ^ n | _ -> ""
                    in
                    Printf.sprintf "_ax%i%s" Stdlib.(incr admitted; !admitted)
                      m_name
                  in
                  (* Create a symbol with the same type as the metavariable *)
                  let ss, sym =
                    Console.out 3 (red "(symb) add axiom %a: %a\n")
                      pp_uid name pp_term !(m.meta_type);
                    add_symbol ss Public Const Eager true (Pos.none name)
                      !(m.meta_type) [] None
                  in
                  (* Create the value which will be substituted for the
                     metavariable. This value is [sym x0 ... xn] where [xi]
                     are variables that will be substituted by the terms of
                     the explicit substitution of the metavariable. *)
                  let meta_value =
                    let vars =
                      let mk_var i =
                        Bindlib.new_var mkfree (Printf.sprintf "x%i" i)
                      in
                      Array.init m.meta_arity mk_var
                    in
                    let v = Array.to_list vars |> List.map _Vari in
                    let ax = _Appl_symb sym v in
                    Bindlib.(bind_mvar vars ax |> unbox)
                  in
                  Meta.set m meta_value; ss
                in
                (* [admit_meta ss m] adds as many axioms as needed to
                   instantiate metavariable [m] by a fresh axiom added to the
                   signature [ss]. Metavariable [m] is set to this new axiom
                   in the process. If [m] is already set to a value, nothing
                   is done. *)
                let admit_meta ss m =
                  let ss = Stdlib.ref ss in
                  (* [admit ms m] adds recursively axioms to admit the
                     metavariables on which [m] depends, and then admits
                     [m]. *)
                  let rec admit ms m =
                    (* This assertion should be ensured by the typechecking
                       algorithm. *)
                    assert (not (MetaSet.mem m ms));
                    LibTerm.Meta.iter true (admit (MetaSet.add m ms))
                      !(m.meta_type);
                    Stdlib.(ss := add_axiom !ss m)
                  in
                  admit MetaSet.empty m; Stdlib.(!ss)
                in
                (* [admit_goal ss g] admits typing goal [g] by adding axioms
                   into signature state [ss]. *)
                let admit_goal ss g =
                  match g with Unif _ -> ss | Typ g ->
                  match !(g.goal_meta.meta_value) with
                  | Some _ -> ss
                  | None -> admit_meta ss g.goal_meta
                in
                (* Add an axiom per metavariable *)
                let ss = List.fold_left admit_goal ss ps.proof_goals in
                (* Add the symbol in the signature with a warning. *)
                Console.out 3 (red "(symb) add %a : %a\n")
                  pp_uid id pp_term a;
                wrn pe.pos "Proof admitted.";
                fst (add_symbol ss expo prop mstrat true p_sym_nam a impl t)
            | P_proof_end ->
                (* Check that no metavariable remains. *)
                if LibTerm.Meta.has true a then
                  (fatal_msg "The type of %a has unsolved metavariables.\n"
                     pp_uid id;
                   fatal pe.pos "We have %a : %a." pp_uid id pp_term a);
                (match t with
                 | Some(t) when LibTerm.Meta.has true t ->
                     fatal_msg
                       "The definition of %a has unsolved metavariables.\n"
                       pp_uid id;
                     fatal pe.pos "We have %a : %a ≔ %a."
                       pp_uid id pp_term a pp_term t
                 | _ -> ());
                (* Check that the proof is indeed finished. *)
                if not (finished ps) then
                  (Console.out 1 "%a" Proof.pp_goals ps;
                   fatal pe.pos "The proof is not finished.");
                (* Add the symbol in the signature. *)
                Console.out 3 (red "(symb) add %a : %a\n")
                  pp_uid id pp_term a;
                fst (add_symbol ss expo prop mstrat opaq p_sym_nam a impl t)
      in
      (* Create proof state. *)
      let ps = {proof_name = p_sym_nam; proof_term; proof_goals} in
      (* Apply tac_solve. *)
      let ps = Tactic.tac_solve pos ps in
      (* Add proof_term as focused goal. *)
      let ps =
        match proof_term with
        | None -> ps
        | Some m -> {ps with proof_goals = Goal.of_meta m :: ps.proof_goals}
      in
      (* Apply tac_refine in case of a definition. *)
      let ps =
        match pt, t with
        | Some pt, Some t ->
            (match ps.proof_goals with
             | Typ gt :: gs -> Tactic.tac_refine pt.pos ps gt gs t
             | _ -> assert false)
        | _, _ -> ps
      in
      if p_sym_prf = None && not (finished ps) then wrn pos
        "Some metavariables could not be solved: a proof must be given";
      { pdata_stmt_pos=p_sym_nam.pos; pdata_p_state=ps; pdata_tactics=ts
      ; pdata_finalize=finalize; pdata_end_pos=pe.pos; pdata_expo }
    in
    (ss, Some(data), None)

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Stdlib.ref infinity

(** [command compile ss cmd] adds to the previous [command] some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle : (Path.t -> Sign.t) -> sig_state -> p_command ->
   sig_state * proof_data option * Query.result =
 fun compile ss ({pos;_} as cmd) ->
  Print.sig_state := ss;
  try
    let (tm, ss) = time (handle compile ss) cmd in
    if Stdlib.(tm >= !too_long) then
      wrn pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal pos "Error on command.\n%s" m
  | e                           ->
      fatal pos "Uncaught exception: %s." (Printexc.to_string e)
