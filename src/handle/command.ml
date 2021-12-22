(** Handling of commands. *)

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
open Sig_state
open Scope
open Print
open Proof

(** Type alias for a function that compiles a Lambdapi module. *)
type compiler = Path.t -> Sign.t

(** Register a check for the type of the builtin symbols "0" and "+1". *)
let _ =
  (* [eq_noexn t u] tries to unify the terms [t] and [u]. *)
  let eq_noexn : term -> term -> bool = fun t u ->
    let p = new_problem() in p := {!p with to_solve = [[], t, u]};
    Unif.solve_noexn p && !p.unsolved = [] && !p.metas = MetaSet.empty
  in
  let register = Builtin.register_expected_type eq_noexn pp_term in
  let expected_zero_type ss _pos =
    try
      match !((StrMap.find "+1" ss.builtins).sym_type) with
      | Prod(a,_) -> a
      | _ -> assert false
    with Not_found -> mk_Meta (LibMeta.fresh (new_problem()) mk_Type 0, [||])
  in
  register "0" expected_zero_type;
  let expected_succ_type ss _pos =
    let typ_0 =
      try lift !((StrMap.find "0" ss.builtins).sym_type)
      with Not_found -> _Meta (LibMeta.fresh (new_problem()) mk_Type 0) [||]
    in
    Bindlib.unbox (_Impl typ_0 typ_0)
  in
  register "+1" expected_succ_type

(** [handle_open ss p] handles the command [open p] with [ss] as the
   signature state. On success, an updated signature state is returned. *)
let handle_open : sig_state -> p_path -> sig_state =
  fun ss {elt=p;pos} ->
  (* Check that [p] is not an alias. *)
  match p with
  | [a] when StrMap.mem a ss.alias_path ->
    fatal pos "Module aliases cannot be open."
  | _ ->
  (* Check that [p] has been required. *)
  if not (Path.Map.mem p !(ss.signature.sign_deps)) then
    fatal pos "Module %a needs to be required first." pp_path p;
  (* Obtain the signature corresponding to [p]. *)
  open_sign ss (Path.Map.find p !(Sign.loaded))

(** [handle_require b ss p] handles the command [require p] (or [require
   open p] if b is true) with [ss] as the signature state and [compile] the
   main compile function (passed as argument to avoid cyclic dependencies).
   On success, an updated signature state is returned. *)
let handle_require : compiler -> bool -> sig_state -> p_path -> sig_state =
  fun compile b ss {elt=p;pos} ->
  (* Check that the module has not already been required. *)
  if Path.Map.mem p !(ss.signature.sign_deps) then
    fatal pos "Module %a is already required." pp_path p;
  (* Compile required path (adds it to [Sign.loaded] among other things) *)
  ignore (compile p);
  (* Add the dependency (it was compiled already while parsing). *)
  ss.signature.sign_deps
    := Path.Map.add p StrMap.empty !(ss.signature.sign_deps);
  if b then open_sign ss (Path.Map.find p !(Sign.loaded)) else ss

(** [handle_require_as compile ss p id] handles the command
    [require p as id] with [ss] as the signature state and [compile] the main
    compilation function passed as argument to avoid cyclic dependencies. On
    success, an updated signature state is returned. *)
let handle_require_as : compiler -> sig_state -> p_path -> p_ident ->
  sig_state =
  fun compile ss ({elt=p;_} as mp) {elt=id;_} ->
  let ss = handle_require compile false ss mp in
  let alias_path = StrMap.add id p ss.alias_path in
  let path_alias = Path.Map.add p id ss.path_alias in
  {ss with alias_path; path_alias}

(** [handle_modifiers ms] verifies that the modifiers in [ms] are compatible.
    If so, they are returned as a tuple. Otherwise, it fails. *)
let handle_modifiers : p_modifier list -> prop * expo * match_strat =
  fun ms ->
  let rec get_modifiers ((props, expos, strats) as acc) = function
    | [] -> acc
    | {elt=P_prop _;_} as p::ms -> get_modifiers (p::props, expos, strats) ms
    | {elt=P_expo _;_} as e::ms -> get_modifiers (props, e::expos, strats) ms
    | {elt=P_mstrat _;_} as s::ms ->
        get_modifiers (props, expos, s::strats) ms
    | {elt=P_opaq;_}::ms -> get_modifiers acc ms
  in
  let props, expos, strats = get_modifiers ([],[],[]) ms in
  let prop =
    match props with
    | [{elt=P_prop (Assoc b);_};{elt=P_prop Commu;_}]
    | [{elt=P_prop Commu;_};{elt=P_prop (Assoc b);_}] -> AC b
    | _::{pos;_}::_ -> fatal pos "Incompatible or duplicated properties."
    | [{elt=P_prop (Assoc _);pos}] ->
        fatal pos "Associativity alone is not allowed as \
                   you can use a rewriting rule instead."
    | [{elt=P_prop p;_}] -> p
    | [] -> Defin
    | _ -> assert false
  in
  let expo =
    match expos with
    | _::{pos;_}::_ ->
        fatal pos "Incompatible or duplicated exposition markers."
    | [{elt=P_expo e;_}] -> e
    | [] -> Public
    | _ -> assert false
  in
  let strat =
    match strats with
    | _::{pos;_}::_ ->
        fatal pos "Incompatible or duplicated matching strategies."
    | [{elt=P_mstrat s;_}] -> s
    | [] -> Eager
    | _ -> assert false
  in
  (prop, expo, strat)

(** [handle_rule ss syms r] checks rule [r], adds it in [ss] and returns the
   set [syms] extended with the symbol [s] defined by [r]. However, it does
   not update the decision tree of [s]. *)
let handle_rule : sig_state -> p_rule -> sym = fun ss r ->
  Console.out 3 (Color.cya "%a") Pos.pp r.pos;
  Console.out 4 "%a" (Pretty.rule "rule") r;
  let pr = scope_rule false ss r in
  let sym = pr.elt.pr_sym in
  if !(sym.sym_def) <> None then
    fatal pr.pos "No rewriting rule can be given on the defined symbol %a."
      pp_sym sym;
  let rule = Tool.Sr.check_rule pr in
  Sign.add_rule ss.signature sym rule;
  Console.out 2 (Color.red "rule %a") pp_rule (sym, rule);
  sym

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
  let impl = Syntax.get_impl_term typ in
  (* We scope the type of the declaration. *)
  let p = new_problem() in
  let typ =
    (if xs = [] then scope_term ~typ:true else scope_term_with_params)
      (expo = Privat) ss Env.empty p (fun _ -> None) (fun _ -> None) typ
  in
  (* We check that [typ] is typable by a sort. *)
  Query.check_sort pos p [] typ;
  (* We check that no metavariable remains. *)
  if !p.metas <> MetaSet.empty then begin
    fatal_msg "The type of %a has unsolved metavariables.@." pp_uid name;
    fatal pos "We have %a : %a." pp_uid name pp_term typ
  end;
  (* Actually add the symbol to the signature and the state. *)
  Console.out 2 (Color.red "symbol %a : %a") pp_uid name pp_term typ;
  let r = add_symbol ss expo prop mstrat false id typ impl None in
  Print.sig_state := fst r; r

(** Representation of a yet unchecked proof. The structure is initialized when
    the proof mode is entered, and its finalizer is called when the proof mode
    is exited (i.e., when a terminator like “end” is used).  Note that tactics
    do not work on this structure directly,  although they act on the contents
    of its [pdata_state] field. *)
type proof_data =
  { pdata_sym_pos  : Pos.popt (** Position of the declared symbol. *)
  ; pdata_state    : proof_state (** Proof state. *)
  ; pdata_proof    : p_proof (** Proof. *)
  ; pdata_finalize : sig_state -> proof_state -> sig_state (** Finalizer. *)
  ; pdata_end_pos  : Pos.popt (** Position of the proof's terminator. *)
  ; pdata_prv      : bool (** [true] iff private symbols are allowed. *) }

(** Representation of a command output. *)
type cmd_output = sig_state * proof_data option * Query.result

(** [get_proof_data compile ss cmd] tries to handle the command [cmd] with
    [ss] as the signature state and [compile] as the main compilation function
    processing lambdapi modules (it is passed as argument to avoid cyclic
    dependencies). On success, an updated signature state is returned.  When
    [cmd] leads to entering the proof mode,  a [proof_data] is also  returned.
    This structure contains the list of the tactics to be executed, as well as
    the initial state of the proof.  The checking of the proof is then handled
    separately. Note that [Fatal] is raised in case of an error. *)
let get_proof_data : compiler -> sig_state -> p_command -> cmd_output =
  fun compile ss ({elt; pos} as cmd) ->
  Console.out 3 (Color.cya "%a") Pos.pp pos;
  Console.out 4 "%a" Pretty.command cmd;
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
      Console.out 2 "builtin \"%s\" ≔ %a" s pp_sym sym;
      (add_builtin ss s sym, None, None)
  | P_notation(qid,n) ->
      let sym = find_sym ~prt:true ~prv:true ss qid in
      Console.out 2 "notation %a %a" pp_sym sym pp_notation n;
      (add_notation ss sym n, None, None)
  | P_unif_rule(h) ->
      (* Approximately same processing as rules without SR checking. *)
      let pur = (scope_rule true ss h).elt in
      let urule = Scope.rule_of_pre_rule pur in
      Sign.add_rule ss.signature Unif_rule.equiv urule;
      Tree.update_dtree Unif_rule.equiv;
      Console.out 2 "unif_rule %a" pp_unif_rule (Unif_rule.equiv, urule);
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
          Console.out 2 (Color.red "symbol %a : %a")
            pp_uid rec_name pp_term rec_typ;
          let id = Pos.make pos rec_name in
          let r = add_symbol ss expo Defin Eager false id rec_typ [] None
          in Print.sig_state := fst r; r
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
    (* We check that the identifier is not already used. *)
    let {elt=id; _} = p_sym_nam in
    if Sign.mem ss.signature id then
      fatal p_sym_nam.pos "Symbol %a already exists." pp_uid id;
    (* Check that this is a syntactically valid symbol declaration. *)
    begin
      match p_sym_typ, p_sym_def, p_sym_trm, p_sym_prf with
      | None, true, None, Some _ -> fatal pos "missing type"
      |    _, true, None, None   -> fatal pos "missing definition"
      | _ -> ()
    end;
    (* Verify modifiers. *)
    let prop, expo, mstrat = handle_modifiers p_sym_mod in
    let opaq = List.exists Syntax.is_opaq p_sym_mod in
    let pdata_prv = expo = Privat || (p_sym_def && opaq) in
    (match p_sym_def, opaq, prop, mstrat with
     | false, true, _, _ -> fatal pos "Symbol declarations cannot be opaque."
     | true, _, Const, _ -> fatal pos "Definitions cannot be constant."
     | true, _, _, Sequen ->
         fatal pos "Definitions cannot have matching strategies."
     | _ -> ());
    (* Problem recording metavariables and constraints. *)
    let p = new_problem() in
    (* Scoping the definition and the type. *)
    (* If there are parameters and both a type and a definition, then we use
       scope_term_with_params instead of scope_term, so that no warning is
       issued during scoping if a parameter is unused in the type or in the
       definition. In this case, this verification must therefore be done
       afterwards. *)
    let scope ?(typ=false) =
      (if p_sym_arg = [] || p_sym_typ = None || p_sym_trm = None
       then scope_term ~typ
       else scope_term_with_params)
        (expo = Privat) ss Env.empty p (fun _ -> None) (fun _ -> None)
    in
    (* Scoping function keeping track of the position. *)
    let scope ?(typ=false) t = Pos.make t.pos (scope ~typ t) in
    (* Desugaring of parameters and scoping of [p_sym_trm]. *)
    let pt, t =
      match p_sym_trm with
      | Some pt ->
          let pt =
            if p_sym_arg = [] then pt
            else let pos = Pos.(cat (end_pos p_sym_nam.pos) pt.pos) in
                 Pos.make pos (P_Abst(p_sym_arg, pt))
          in Some pt, Some (scope pt)
      | None -> None, None
    in
    (* Desugaring of parameters, scoping of [p_sym_typ], and computation
       of implicit arguments. *)
    let a, impl =
      match p_sym_typ with
      | None ->
        let impl =
          match pt with
          | None -> assert false
          | Some pt -> Syntax.get_impl_term pt
        in None, impl
      | Some a ->
          let a =
            if p_sym_arg = [] then a
            else let pos = Pos.(cat (end_pos p_sym_nam.pos) a.pos) in
                 Pos.make pos (P_Prod(p_sym_arg, a))
          in Some (scope ~typ:true a), Syntax.get_impl_term a
    in
    (* If there are parameters, output a warning if they are not used. *)
    if p_sym_arg <> [] then
      begin match a, t with
      | Some a, Some t ->
          let rec binders_warn k ty te =
            if k <= 0 then () else
              match ty, te with
              | Prod(_, by), Abst(_, be) ->
                  let x, ty, te = Bindlib.unbind2 by be in
                  if Bindlib.(binder_constant by && binder_constant be) then
                    wrn pos "Variable [%a] could be replaced by [_]."
                      pp_var x;
                  binders_warn (k-1) ty te
              | _ -> assert false
          in binders_warn (Syntax.nb_params p_sym_arg) a.elt t.elt
      | _ -> ()
      end;
    (* Build proof data. *)
    let pdata =
      (* Type of the symbol. *)
      let a =
        match a with
        | Some {elt=t;pos} -> (* Check that the given type is well sorted. *)
            Query.check_sort pos p [] t; t
        | None -> (* If no type is given, infer it from the definition. *)
            match t with
            | None -> assert false
            | Some {elt=t;pos} -> Query.infer pos p [] t
      in
      (* Get tactics and proof end. *)
      let pdata_proof, pe =
        match p_sym_prf with
        | None -> [], Pos.make (Pos.end_pos pos) P_proof_end
        | Some (ts, pe) -> ts, pe
      in
      (* Initialize proof state. *)
      Console.State.push ();
      (* Build finalizer. *)
      let pdata_finalize ss ps =
        Console.State.pop ();
        match pe.elt with
        | P_proof_abort -> wrn pe.pos "Proof aborted."; ss
        | P_proof_admitted ->
            (* If the proof is finished, display a warning. *)
            let ss =
            if finished ps then
              ( wrn pe.pos "The proof is finished. Use 'end' instead."; ss )
            else
              match ps.proof_term with
              | Some m when opaq ->
                  (* We admit the initial goal only. *)
                  Tactic.admit_meta ss m
              | _ ->
                  (* We admit all the remaining typing goals. *)
                  let admit_goal ss g =
                    match g with
                    | Unif _ -> ss
                    | Typ gt ->
                        let m = gt.goal_meta in
                        match !(m.meta_value) with
                        | None -> Tactic.admit_meta ss m
                        | Some _ -> ss
                  in List.fold_left admit_goal ss ps.proof_goals
            in
            (* Add the symbol in the signature with a warning. *)
            Console.out 2 (Color.red "symbol %a : %a") pp_uid id pp_term a;
            wrn pe.pos "Proof admitted.";
            let t = Option.map (fun t -> t.elt) t in
            fst (add_symbol ss expo prop mstrat opaq p_sym_nam a impl t)
        | P_proof_end ->
            (* Check that the proof is indeed finished. *)
            if not (finished ps) then
              fatal pe.pos "The proof is not finished.";
            (* Add the symbol in the signature. *)
            Console.out 2 (Color.red "symbol %a : %a") pp_uid id pp_term a;
            let t = Option.map (fun t -> t.elt) t in
            fst (add_symbol ss expo prop mstrat opaq p_sym_nam a impl t)
      in
      (* Create the proof state. *)
      let pdata_state =
        let proof_goals = Proof.add_goals_of_problem p [] in
        if p_sym_def then
          (* Add a new focused goal and refine on it. *)
          let m = LibMeta.fresh p ~name:id a 0 in
          let g = Goal.of_meta m in
          let ps = {proof_name = p_sym_nam; proof_term = Some m;
                    proof_goals = g :: proof_goals} in
          match pt, t with
          | Some pt, Some t ->
              let gt = match g with Typ gt -> gt | _ -> assert false in
              (*TODO there is no need for tac_refine to type-check [t] again
                 if [a] is the type infered from [t]. *)
              Tactic.tac_refine pt.pos ps gt proof_goals p t.elt
          | _, _ -> Tactic.tac_solve pos ps
        else
          let ps = {proof_name = p_sym_nam; proof_term = None; proof_goals} in
          Tactic.tac_solve pos ps
      in
      if p_sym_prf = None && not (finished pdata_state) then wrn pos
        "Some metavariables could not be solved: a proof must be given";
      { pdata_sym_pos=p_sym_nam.pos; pdata_state; pdata_proof
      ; pdata_finalize; pdata_end_pos=pe.pos; pdata_prv }
    in
    (ss, Some pdata, None)

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Stdlib.ref infinity

(** [get_proof_data compile ss cmd] adds to the previous [command] some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let get_proof_data : compiler -> sig_state -> p_command -> cmd_output =
  fun compile ss ({pos;_} as cmd) ->
  Print.sig_state := ss;
  try
    let (tm, ss) = Extra.time (get_proof_data compile ss) cmd in
    if Stdlib.(tm >= !too_long) then
      wrn pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal pos "Error on command.@.%s" m
  | Fatal(Some(None)   ,m)      -> fatal pos "Error on command.@.%s" m
  | e                           ->
      fatal pos "Uncaught exception: %s." (Printexc.to_string e)

(** [handle compile_mod ss cmd] retrieves proof data from [cmd] (with
    {!val:get_proof_data}) and handles proofs using functions from
    {!module:Tactic} The function [compile_mod] is used to compile required
    modules recursively. *)
let handle : compiler -> Sig_state.t -> Syntax.p_command -> Sig_state.t =
  fun compile_mod ss cmd ->
  LibMeta.reset_meta_counter ();
  (* We provide the compilation function to the handle commands, so that
     "require" is able to compile files. *)
  let (ss, p, _) = get_proof_data compile_mod ss cmd in
  match p with
  | None -> ss
  | Some d ->
    let ss, ps, _ =
      fold_proof (Tactic.handle d.pdata_prv)
        (ss, d.pdata_state, None) d.pdata_proof
    in d.pdata_finalize ss ps
