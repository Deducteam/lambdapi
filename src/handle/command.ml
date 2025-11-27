(** Handling of commands. *)

open Lplib open Base open Extra
open Timed
open Common open Error open Pos
open Core open Term open Sign open Sig_state open Print
open Parsing open Syntax open Scope
open Proof
open Goal

(** Type alias for a function that compiles a Lambdapi module. *)
type compiler = Path.t -> Sign.t

(** Register a check for the type of the builtin symbols "nat_zero" and
    "nat_succ". *)
let _ =
  (* [eq_noexn t u] tries to unify the terms [t] and [u]. *)
  let eq_noexn : term -> term -> bool = fun t u ->
    let p = new_problem() in p := {!p with to_solve = [[], t, u]};
    Unif.solve_noexn p && !p.unsolved = [] && !p.metas = MetaSet.empty
  in
  let register = Builtin.register_expected_type eq_noexn term in
  let expected_zero_type ss _pos =
    try
      match !((StrMap.find "nat_succ" ss.builtins).sym_type) with
      | Prod(a,_) -> a
      | _ -> assert false
    with Not_found -> mk_Meta (LibMeta.fresh (new_problem()) mk_Type 0, [||])
  in
  register "nat_zero" expected_zero_type;
  let expected_succ_type ss _pos =
    let typ_0 =
      try !((StrMap.find "nat_zero" ss.builtins).sym_type)
      with Not_found ->
        mk_Meta (LibMeta.fresh (new_problem()) mk_Type 0, [||])
    in
    mk_Arro (typ_0, typ_0)
  in
  register "nat_succ" expected_succ_type

(** [rec_open record ss p] opens [p] and all its dependencies marked as
    open. It assumes that [p] and all its dependencies are already
    loaded. Records open modules if [record]. On success, an updated signature
    state is returned. *)
let rec rec_open : bool -> sig_state -> Path.t -> sig_state =
  fun record ss p ->
  if Path.Set.mem p ss.open_paths then ss
  else
    begin
      match Path.Map.find_opt p !loaded with
      | None -> assert false
      | Some sign ->
          (* Recursively open the dependencies of [p] declared as open. *)
          let f p d ss = if d.dep_open then rec_open record ss p else ss in
          let ss = Path.Map.fold f !(sign.sign_deps) ss in
          (* Record that [p] must be open if [record]. *)
          if record then
            begin
              let f = function
                | None -> assert false
                | Some ({dep_open=false;_} as d) ->
                    Some {d with dep_open=true}
                | x -> x
              in
              let deps = ss.signature.sign_deps in
              deps := Path.Map.update p f !deps
            end;
          (* Add symbols of [p] in scope. *)
          open_sign ss sign
    end

let handle_open : bool -> sig_state -> p_path -> sig_state =
  fun prv ss {elt=p;pos} ->
  (* Check that [p] is not an alias. *)
  match p with
  | [a] when StrMap.mem a ss.alias_path ->
      fatal pos "Module aliases cannot be open."
  | _ ->
      (* Check that [p] has been required. *)
      match Path.Map.find_opt p !loaded with
      | None -> fatal pos "Module \"%a\" needs to be required first." path p
      | Some _ -> rec_open (not prv) ss p

(** [rec_require compile ss p] handles the command [require p] with [ss] as
    signature state and [compile] as compilation function (passed as argument
    to avoid cyclic dependencies). On success, an updated signature state is
    returned. *)
let rec rec_require : compiler -> sig_state -> Path.t -> sig_state =
  fun compile ss p ->
  if p = Sign.Ghost.path then ss
  else
    let deps = ss.signature.sign_deps in
    if Path.Map.mem p !deps then ss
    else
      begin
        (* Compile [p] (this adds it to [Sign.loaded]). *)
        let sign = compile p in
        (* Recurse on the dependencies of [p]. *)
        let f p _ ss = rec_require compile ss p in
        let ss = Path.Map.fold f !(sign.sign_deps) ss in
        (* Add builtins of [p] in [ss]. *)
        let f _k _v1 v2 = Some v2 in (* hides previous symbols *)
        let builtins = StrMap.union f ss.builtins !(sign.sign_builtins) in
        let ss = {ss with builtins} in
        (* Add [p] in dependencies. *)
        let dep = {dep_symbols=StrMap.empty; dep_open=false} in
        deps := Path.Map.add p dep !deps;
        ss
      end

(** [handle_require_as compile ss p id] handles the command [require p as id]
    with [ss] as the signature state and [compile] as compilation function
    (passed as argument to avoid cyclic dependencies). On success, an updated
    signature state is returned. *)
let handle_require_as :
      compiler -> sig_state -> p_path -> p_ident -> sig_state =
  fun compile ss {elt=p;_} {elt=id;_} ->
  if Path.Map.mem p !(ss.signature.sign_deps) then ss
  else
    begin
      let ss = rec_require compile ss p in
      let alias_path = StrMap.add id p ss.alias_path in
      let path_alias = Path.Map.add p id ss.path_alias in
      {ss with alias_path; path_alias}
    end

(** [handle_require compile bo ss p] handles the command [require p] with
    [compile] as compilation function (passed as argument to avoid cyclic
    dependencies), [bo=Some(true)] if the command is [require private open p],
    [bo=Some(false)] if the command is [require open p], and [ss] as signature
    state. On success, an updated signature state is returned. *)
let handle_require compile bo ss {elt=p;_} =
  let ss = rec_require compile ss p in
  match bo with
  | Some prv -> rec_open (not prv) ss p
  | None -> ss

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

(** [handle_inductive_symbol ss e p strat x xs a] handles the command
    [e p strat symbol x xs : a] with [ss] as the signature state.
    The command is at position [pos].
    On success, an updated signature state and the new symbol are returned. *)
let handle_inductive_symbol : sig_state -> expo -> prop -> match_strat
    -> p_ident -> popt -> p_params list -> p_term -> sig_state * sym =
  fun ss expo prop mstrat ({elt=name;pos} as id) declpos xs typ ->
  (* We check that [id] is not already used. *)
  if Sign.mem ss.signature name then
    fatal pos "Symbol %a already exists." uid name;
  (* Desugaring of arguments of [typ]. *)
  let typ = if xs = [] then typ else Pos.none (P_Prod(xs, typ)) in
  (* Obtaining the implicitness of arguments. *)
  let impl = Syntax.get_impl_term typ in
  (* We scope the type of the declaration. *)
  let p = new_problem() in
  let typ = scope_term ~typ:true (expo = Privat) ss Env.empty typ in
  (* We check that [typ] is typable by a sort. *)
  let (typ,  _) = Query.check_sort pos p [] typ in
  (* We check that no metavariable remains. *)
  if !p.metas <> MetaSet.empty then begin
    fatal_msg "The type of %a has unsolved metavariables.@." uid name;
    fatal pos "We have %a : %a." uid name term typ
  end;
  (* Actually add the symbol to the signature and the state. *)
  Console.out 2 (Color.gre "symbol %a : %a") uid name term typ;
  let r =
   Sig_state.add_symbol ss expo prop mstrat false id declpos typ impl None in
  sig_state := fst r; r

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

(** [sr_check] indicates whether subject-reduction should be checked. *)
let sr_check = Stdlib.ref true

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
  | P_opaque qid ->
    let s = Sig_state.find_sym ~prt:true ~prv:true ss qid in
    if !(s.sym_opaq) then fatal pos "Symbol already opaque.";
    s.sym_opaq := true;
    (ss, None, None)
  | P_query(q) -> (ss, None, Query.handle ss None q)
  | P_require(bo,ps) ->
      (List.fold_left (handle_require compile bo) ss ps, None, None)
  | P_require_as(p,id) -> (handle_require_as compile ss p id, None, None)
  | P_open(b,ps) -> (List.fold_left (handle_open b) ss ps, None, None)
  | P_rules(rs) ->
    (* Scope rules, and check that they preserve typing. Return the list of
       rules [srs] and also a [map] mapping every symbol defined by a rule
       of [srs] to its defining rules. *)
      let handle_rule r (srs, map) =
        let sr = scope_rule false ss r in
        let (s,r) as sr =
          if Stdlib.(!sr_check) then Tool.Sr.check_rule r.pos sr else sr in
        let h = function Some rs -> Some(r::rs) | None -> Some[r] in
        sr::srs, SymMap.update s h map
      in
      (* The order of rules must be kept between [rs] and [srs].
         That is, the following assertion should hold
         [assert (srs = List.map (check_rule ss) rs);] if we could compare
         functional values. Failure to keep that invariant breaks some
         evaluation strategies. *)
      let srs, map = List.fold_right handle_rule rs ([], SymMap.empty) in
      (* /!\ Update decision trees without adding the rules themselves. It is
         important for local confluence checking. *)
      SymMap.iter Tree.update_dtree map;
      let sign = ss.signature in
      (* Local confluence checking. *)
      Tool.Lcr.check_cps pos sign srs map;
      (* Add rules in the signature. *)
      SymMap.iter (Sign.add_rules ss.signature) map;
      if !Console.verbose >= 2 then
        List.iter (Console.out 2 (Color.gre "rule %a") sym_rule)
          (List.rev srs);
      (* Update critical pair positions. *)
      sign.Sign.sign_cp_pos :=
        Tool.Lcr.update_cp_pos pos !(sign.Sign.sign_cp_pos) map;
      (ss, None, None)
  | P_builtin(n,qid) ->
      let s = find_sym ~prt:true ~prv:true ss qid in
      begin
        match StrMap.find_opt n ss.builtins with
        | Some s' when s' == s ->
          fatal pos "Builtin \"%s\" already mapped to %a" n sym s
        | _ ->
          Builtin.check ss pos n s;
          Console.out 2 (Color.gre "builtin \"%s\" ≔ %a") n sym s;
          (Sig_state.add_builtin ss n s, None, None)
      end
  | P_notation(qid,n) ->
      let s = find_sym ~prt:true ~prv:true ss qid in
      (* Check arity. *)
      let expected =
        match n with
        | Prefix _ | Postfix _ | Quant -> 1
        | Infix _ -> 2
        | _ -> assert false
      and real = LibTerm.count_products Eval.whnf [] !(s.sym_type) in
      if real < expected then
        fatal pos "Notation incompatible with the type of %a" sym s;
      (* Check that the notation is compatible with the theory. *)
      begin
        match s.sym_prop, n with
        | (Assoc true | AC true), Infix (Pratter.Right,_)
        | (Assoc false | AC false), Infix (Pratter.Left,_)
          -> fatal pos
               "notation incompatible with symbol property \
                (e.g. infix right notation on left associative symbol)"
        | _ -> ()
      end;
      (* Convert strings into floats. *)
      let float_priority_from_string_priority s =
        try
          if String.contains s '.' then float_of_string s
          else float_of_int (int_of_string s)
        with Failure _ -> fatal pos "Too big number (max is %d)" max_int
      in
      let float_notation_from_string_notation n =
        match n with
        | Prefix s -> Prefix (float_priority_from_string_priority s)
        | Postfix s -> Postfix (float_priority_from_string_priority s)
        | Infix(a,s) -> Infix(a, float_priority_from_string_priority s)
        | Quant -> Quant
        | _ -> assert false
      in
      let n = float_notation_from_string_notation n in
      Console.out 2 (Color.gre "notation %a %a") sym s (notation float) n;
      Sign.add_notation ss.signature s n;
      (ss, None, None)
  | P_unif_rule(h) ->
      (* Approximately same processing as rules without SR checking. *)
      let r = scope_rule true ss h in
      Sign.add_rule ss.signature r;
      Tree.update_dtree Unif_rule.equiv [];
      Console.out 2 (Color.gre "unif_rule %a") sym_rule r;
      (ss, None, None)
  | P_coercion c ->
      let r = scope_rule false ss c in
      Sign.add_rule ss.signature r;
      Tree.update_dtree Coercion.coerce [];
      Console.out 2 (Color.gre "coercion %a") sym_rule r;
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
          (* All inductive types are declared at position [pos]
             so that constructors are declared afterwards. *)
          let id = {id with pos} in
          handle_inductive_symbol ss expo Const Eager id pos params pt in
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
            handle_inductive_symbol ss expo Const Eager id pos
            params pt in
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
          fatal pos "Symbol %a already exists." uid rec_name;
        let (ss, rec_sym) =
          Console.out 2 (Color.gre "symbol %a : %a")
            uid rec_name term rec_typ;
          (* Recursors are declared after the types and constructors. *)
          let pos = after (pos_end pos) in
          let id = Pos.make pos rec_name in
          let r =
            Sig_state.add_symbol ss expo Defin Eager false id
             None rec_typ [] None
          in sig_state := fst r; r
        in
        (ss, rec_sym::rec_sym_list)
      in
      let (ss, rec_sym_list) =
        List.fold_left2 add_recursor (ss, [])
          ind_sym_list_rev rec_typ_list_rev
      in
      (* Add recursor rules in the signature. *)
      let add_rule pr =
        let r = scope_rule false ss pr in
        let r = Tool.Sr.check_rule pos r in
        Sign.add_rule ss.signature r;
        Console.out 2 (Color.gre "rule %a") sym_rule r
      in
      no_wrn (Inductive.iter_rec_rules pos ind_list vs ind_pred_map) add_rule;
      List.iter (fun s -> Tree.update_dtree s []) rec_sym_list;
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
      fatal p_sym_nam.pos "Symbol %a already exists." uid id;
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
    let pdata_prv = opaq || expo = Privat in
    (match p_sym_def, opaq, prop, mstrat with
     | false, true, _, _ -> fatal pos "Symbol declarations cannot be opaque."
     | true, _, Const, _ -> fatal pos "Definitions cannot be constant."
     | true, _, _, Sequen ->
         fatal pos "Definitions cannot have matching strategies."
     | _ -> ());
    (* Scoping the definition and the type. *)
    let scope ?(typ=false) = scope_term ~typ pdata_prv ss Env.empty in
    (* Scoping function keeping track of the position. *)
    let scope ?(typ=false) t = Pos.make t.pos (scope ~typ t) in
    (* Desugaring of parameters and scoping of [p_sym_trm]. *)
    let pt, t =
      match p_sym_trm with
      | Some pt ->
          let pt =
            if p_sym_arg = [] then pt
            else let pos = Pos.(cat (pos_end p_sym_nam.pos) pt.pos) in
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
            else let pos = Pos.(cat (pos_end p_sym_nam.pos) a.pos) in
                 Pos.make pos (P_Prod(p_sym_arg, a))
          in Some (scope ~typ:true a), Syntax.get_impl_term a
    in
    (* Problem recording metavariables and constraints. *)
    let p = new_problem() in
    (* Build proof data. *)
    let pdata =
      (* Type of the symbol. *)
      let t, a =
        match a with
        | Some {elt=a;pos} -> (* Check that the given type is well sorted. *)
          begin match Infer.check_sort_noexn p [] a with
            | None -> fatal pos "%a@ cannot be typed by a sort" term a
            | Some (a,_) ->
              let t =
                match t with
                | None -> None
                | Some {elt=t;pos} ->
                  match Infer.check_noexn p [] t a with
                  | None ->
                    fatal pos "%a@ cannot be of type@ %a" term t term a
                  | Some t -> Some (Pos.make pos t)
              in
              (t, a)
          end
        | None -> (* If no type is given, infer it from the definition. *)
          match t with
          | None -> assert false
          | Some {elt=t;pos} ->
            match Infer.infer_noexn p [] t with
            | None -> fatal pos "%a@ is not typable" term t
            | Some (t,a) -> Some (Pos.make pos t), a
      in
      (* Get tactics and proof end. *)
      let pdata_proof, pe =
        match p_sym_prf with
        | None -> [], Pos.make (Pos.pos_end pos) P_proof_end
        | Some (ts, pe) -> ts, pe
      in
      (* Build finalizer. *)
      let declpos = Pos.cat pos (Option.bind p_sym_typ (fun x -> x.pos)) in
      let pdata_finalize ss ps =
        match pe.elt with
        | P_proof_abort -> wrn pe.pos "Proof aborted."; ss
        | P_proof_admitted ->
            if finished ps then
              fatal pe.pos "The proof is finished. Use 'end' instead.";
            (* Admit all the remaining typing goals. *)
            let admit_goal g =
              match g with
              | Unif _ -> fatal pos "Cannot admit unification goals."
              | Typ gt ->
                let m = gt.goal_meta in
                match !(m.meta_value) with
                | None -> Tactic.admit_meta ss p_sym_nam.pos m
                | Some _ -> ()
            in
            List.iter admit_goal ps.proof_goals;
            (* Add the symbol in the signature with a warning. *)
            Console.out 2 (Color.gre "symbol %a : %a") uid id term a;
            wrn pe.pos "Proof admitted.";
            (* Keep the definition only if the symbol is not opaque. *)
            let d =
              if opaq then None else
                Option.map (fun m -> unfold (mk_Meta(m,[||]))) ps.proof_term
            in
            (* Add the symbol in the signature. *)
            fst (Sig_state.add_symbol
                   ss expo prop mstrat opaq p_sym_nam declpos a impl d)
        | P_proof_end ->
            (* Check that the proof is indeed finished. *)
            if not (finished ps) then
              fatal pe.pos "The proof is not finished:@.%a" goals ps;
            (* Keep the definition only if the symbol is not opaque. *)
            let d =
              if opaq then None else
                Option.map (fun m -> unfold (mk_Meta(m,[||]))) ps.proof_term
            in
            (* Add the symbol in the signature. *)
            Console.out 2 (Color.gre "symbol %a : %a") uid id term a;
            fst (Sig_state.add_symbol
                   ss expo prop mstrat opaq p_sym_nam declpos a impl d)
      in
      (* Create the proof state. *)
      let pdata_state =
        let proof_goals = add_goals_of_problem p [] in
        if p_sym_def then
          (* Add a new focused goal and refine on it. *)
          let m = LibMeta.fresh p a 0 in
          let g = Goal.of_meta m in
          let ps = {proof_name = p_sym_nam; proof_term = Some m;
                    proof_goals = g :: proof_goals} in
          match pt, t with
          | Some pt, Some t ->
              let gt = match g with Typ gt -> gt | _ -> assert false in
              Tactic.tac_refine ~check:false pt.pos ps gt proof_goals p t.elt
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
  sig_state := ss;
  try
    let (tm, ss) = Extra.time (get_proof_data compile ss) cmd in
    if Stdlib.(tm >= !too_long) then
      wrn pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_, _) as e -> raise e
  | Fatal(None         ,m, _)      -> fatal pos "Error on command.@.%s" m
  | Fatal(Some(None)   ,m, _)      -> fatal pos "Error on command.@.%s" m
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
    let ps, _ =
      fold_proof (Tactic.handle ss d.pdata_sym_pos d.pdata_prv)
        (d.pdata_state, None) d.pdata_proof
    in d.pdata_finalize ss ps
