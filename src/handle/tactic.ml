(** Handling of tactics. *)

open Lplib open Extra
open Common open Error open Pos
open Parsing open Syntax
open Core open Term open Print
open Proof
open Timed

(** Logging function for tactics. *)
let log = Logger.make 't' "tact" "tactics"
let log = log.pp

(** Number of admitted axioms in the current signature. Used to name the
    generated axioms. This reference is reset in {!module:Compile} for each
    new compiled module. *)
let admitted_initial_value = min_int
let admitted : int Stdlib.ref = Stdlib.ref admitted_initial_value
let reset_admitted() = Stdlib.(admitted := admitted_initial_value)

(** [add_axiom ss sym_pos m] adds in signature state [ss] a new axiom symbol
    of type [!(m.meta_type)] and instantiate [m] with it. WARNING: It does not
    check whether the type of [m] contains metavariables. Return updated
    signature state [ss] and the new axiom symbol.*)
let add_axiom : Sig_state.t -> popt -> meta -> sym =
  fun ss sym_pos m ->
  let name =
    let i = Stdlib.(incr admitted; !admitted) in
    assert (i<=0);
    Printf.sprintf "_ax%i" (i + max_int)
  in
  (* Create a symbol with the same type as the metavariable *)
  let sym =
    Console.out 1 (Color.red "axiom %a: %a") uid name term !(m.meta_type);
    (* Temporary hack for axioms to have a declaration position in the order
       they are created. *)
    let pos = shift Stdlib.(!admitted) sym_pos in
    let id = Pos.make pos name in
    (* We ignore the new ss returned by Sig_state.add_symbol: axioms do not
       need to be in scope. *)
    snd (Sig_state.add_symbol ss
           Public Defin Eager true id None !(m.meta_type) [] None)
  in
  (* Create the value which will be substituted for the metavariable. This
     value is [sym x0 ... xn] where [xi] are variables that will be
     substituted by the terms of the explicit substitution of the
     metavariable. *)
  let meta_value =
    let vars = Array.init m.meta_arity (new_var_ind "x") in
    let ax = add_args (mk_Symb sym) (List.map mk_Vari (Array.to_list vars)) in
    bind_mvar vars ax
  in
  LibMeta.set (new_problem()) m meta_value; sym

(** [admit_meta ss sym_pos m] adds as many axioms as needed in the signature
   state [ss] to instantiate the metavariable [m] by a fresh axiom added to
   the signature [ss]. *)
let admit_meta : Sig_state.t -> popt -> meta -> unit =
  fun ss sym_pos m ->
  (* [ms] records the metas that we are instantiating. *)
  let rec admit ms m =
    (* This assertion should be ensured by the typechecking algorithm. *)
    assert (not (MetaSet.mem m ms));
    LibMeta.iter true (admit (MetaSet.add m ms)) [] !(m.meta_type);
    ignore (add_axiom ss sym_pos m)
  in
  admit MetaSet.empty m

(** [tac_admit ss pos ps gt] admits typing goal [gt]. *)
let tac_admit: Sig_state.t -> popt -> proof_state -> goal_typ -> proof_state =
  fun ss sym_pos ps gt ->
  admit_meta ss sym_pos gt.goal_meta; remove_solved_goals ps

(** [tac_solve pos ps] tries to simplify the unification goals of the proof
   state [ps] and fails if constraints are unsolvable. *)
let tac_solve : popt -> proof_state -> proof_state = fun pos ps ->
  if Logger.log_enabled() then log "tac_solve";
  (* convert the proof_state into a problem *)
  let gs_typ, gs_unif = List.partition is_typ ps.proof_goals in
  let p = new_problem() in
  let add_meta ms = function
    | Unif _ -> ms
    | Typ gt -> MetaSet.add gt.goal_meta ms
  in
  p := {!p with metas = List.fold_left add_meta MetaSet.empty gs_typ
              ; to_solve = List.rev_map get_constr gs_unif};
  (* try to solve the problem *)
  if not (Unif.solve_noexn p) then
    fatal pos "Unification goals are unsatisfiable.";
  (* compute the new list of goals by preserving the order of initial goals
     and adding the new goals at the end *)
  let non_instantiated g =
    match g with
    | Typ gt when !(gt.goal_meta.meta_value) = None ->
        Some (Goal.simpl Eval.beta_simplify g)
    | _ -> None
  in
  let gs_typ = List.filter_map non_instantiated gs_typ in
  let is_eq_goal_meta m = function
    | Typ gt -> m == gt.goal_meta
    | _ -> assert false
  in
  let add_goal m gs =
    if List.exists (is_eq_goal_meta m) gs_typ then gs
    else Goal.of_meta m :: gs
  in
  let proof_goals =
    gs_typ @ MetaSet.fold add_goal (!p).metas
               (List.map (fun c -> Unif c) (!p).unsolved)
  in
  {ps with proof_goals}

(** [tac_refine pos ps gt gs p t] refines the typing goal [gt] with [t]. [p]
   is the set of metavariables created by the scoping of [t]. *)
let tac_refine : ?check:bool ->
      popt -> proof_state -> goal_typ -> goal list -> problem -> term
      -> proof_state =
  fun ?(check=true) pos ps gt gs p t ->
  if Logger.log_enabled () then log "tac_refine %a" term t;
  let c = Env.to_ctxt gt.goal_hyps in
  (* Check that [t] has the required type. *)
  let t =
    if check then
      match Infer.check_noexn p c t gt.goal_type with
      | None ->
          let ids = Ctxt.names c in let term = term_in ids in
          fatal pos "%a\ndoes not have type\n%a." term t term gt.goal_type
      | Some t -> t
    else t
  in
  if LibMeta.occurs gt.goal_meta c t then fatal pos "Circular refinement.";
  if Logger.log_enabled () then
    log (Color.red "%a ≔ %a") meta gt.goal_meta term t;
  LibMeta.set p gt.goal_meta (bind_mvar (Env.vars gt.goal_hyps) t);
  (* Convert the metas and constraints of [p] not in [gs] into new goals. *)
  tac_solve pos {ps with proof_goals = Proof.add_goals_of_problem p gs}

(** [ind_data t] returns the [ind_data] structure of [s] if [t] is of the
   form [s t1 .. tn] with [s] an inductive type. Fails otherwise. *)
let ind_data : popt -> Env.t -> term -> Sign.ind_data = fun pos env a ->
  let h, ts = get_args (Eval.whnf (Env.to_ctxt env) a) in
  match h with
  | Symb s ->
      let sign = Path.Map.find s.sym_path Sign.(!loaded) in
      begin
        try
          let ind = SymMap.find s !(sign.sign_ind) in
          let _, ts = List.cut ts ind.ind_nb_params (*remove parameters*) in
          let ctxt = Env.to_ctxt env in
          if LibTerm.distinct_vars ctxt (Array.of_list ts) = None
          then fatal pos "%a is not applied to distinct variables." sym s
          else ind
        with Not_found -> fatal pos "%a is not an inductive type." sym s
      end
  | _ ->
      let ids = Env.names env in let term = term_in ids in
      fatal pos "%a is not headed by an inductive type." term a

(** [tac_induction pos ps gt] tries to apply the induction tactic on the
   typing goal [gt]. *)
let tac_induction : popt -> proof_state -> goal_typ -> goal list
    -> proof_state = fun pos ps ({goal_type;goal_hyps;_} as gt) gs ->
  let ctx = Env.to_ctxt goal_hyps in
  match Eval.whnf ctx goal_type with
  | Prod(a,_) ->
      let ind = ind_data pos goal_hyps a in
      let n = ind.ind_nb_params + ind.ind_nb_types + ind.ind_nb_cons in
      let p = new_problem () in
      let metas =
        let fresh_meta _ =
          let mt = LibMeta.make p ctx mk_Type in
          LibMeta.make p ctx mt
        in
        (* Reverse to have goals properly sorted. *)
        List.(rev (init (n - 1) fresh_meta))
      in
      let t = add_args (mk_Symb ind.ind_prop) metas in
      tac_refine pos ps gt gs p t
  | _ ->
      let ids = Ctxt.names ctx in let term = term_in ids in
      fatal pos "[%a] is not a product." term goal_type

(** [get_prod_ids env do_whnf t] returns the list [v1;..;vn] if [do_whnf] is
    true and [whnf t] is of the form [Π v1:A1, .., Π vn:An, u] with [u] not a
    product, or if [do_whnf] is false and [t] is of the form [Π v1:A1, .., Π
    vn:An, u] with [u] not a product. *)
let get_prod_ids env =
  let rec aux acc do_whnf t =
    match get_args t with
    | Prod(_,b), _ ->
        let x,b = unbind b in
        aux (base_name x::acc) do_whnf b
    | _ ->
        if do_whnf then aux acc false (Eval.whnf (Env.to_ctxt env) t)
        else List.rev acc
  in aux []

(** Builtin tactic names. *)
type tactic =
  | T_admit
  | T_and
  | T_apply
  | T_assume
  | T_fail
  | T_generalize
  | T_have
  | T_induction
  | T_orelse
  | T_refine
  | T_reflexivity
  | T_remove
  | T_repeat
  | T_rewrite
  | T_set
  | T_simplify
  | T_simplify_beta
  | T_solve
  | T_symmetry
  | T_try
  | T_why3

type config = (string,tactic) Hashtbl.t

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config (ss:Sig_state.t) (pos:Pos.popt) : config =
  let t = Hashtbl.create 17 in
  let add n v = let s = Builtin.get ss pos n in Hashtbl.add t s.sym_name v in
  add "admit" T_admit;
  add "and" T_and;
  add "apply" T_apply;
  add "assume" T_assume;
  add "fail" T_fail;
  add "generalize" T_generalize;
  add "have" T_have;
  add "induction" T_induction;
  add "orelse" T_orelse;
  add "refine" T_refine;
  add "reflexivity" T_reflexivity;
  add "remove" T_remove;
  add "repeat" T_repeat;
  add "rewrite" T_rewrite;
  add "set" T_set;
  add "simplify" T_simplify;
  add "simplify rule off" T_simplify_beta;
  add "solve" T_solve;
  add "symmetry" T_symmetry;
  add "try" T_try;
  add "why3" T_why3;
  t

(** [p_term pos t] converts the term [t] into a p_term at position [pos]. *)
let p_term (pos:popt): int StrMap.t -> term -> p_term =
  let mk = Pos.make pos in
  let rec term idmap t = Pos.make pos (term_aux idmap t)
  and params idmap x a =
    [Some(Pos.make pos (base_name x))],Some(term idmap a),false
  and term_aux idmap t :p_term_aux =
    match unfold t with
    | Type -> P_Type
    | Symb s ->
        let t = P_Iden(mk(s.sym_path,s.sym_name),true) in
        if !(s.sym_nota) = NoNotation then t else P_Wrap (Pos.make pos t)
    | Vari v -> P_Iden(mk([],base_name v),false)
    | Appl(u,v) -> P_Appl(term idmap u, term idmap v)
    | Prod(a,b) ->
        let (x,b),idmap' = Print.safe_unbind idmap b in
        P_Prod([params idmap x a], term idmap' b)
    | Abst(a,b) ->
        let (x,b),idmap' = Print.safe_unbind idmap b in
        P_Abst([params idmap x a], term idmap' b)
    | LLet(a,t,b) ->
        let (x,b),idmap' = Print.safe_unbind idmap b in
        let id = Pos.make pos (base_name x) in
        P_LLet(id,[],Some(term idmap a),term idmap t,term idmap' b)
    | _ -> fatal pos "Unhandled term expression: %a." Print.term t
  in term

let remove_quotes s = String.sub s 1 (String.length s - 2)

let _ = assert (remove_quotes "\"\"" = "" && remove_quotes "\"ab\"" = "ab")

let p_ident_of_sym (pos:popt) (t:term) :p_ident =
  match unfold t with
  | Symb s when s.sym_path = Sign.Ghost.path
                && String.is_string_literal s.sym_name ->
      Pos.make pos (remove_quotes s.sym_name)
  | _ -> fatal pos "Not a string: %a." term t

let p_ident_of_var (pos:popt) (t:term) :p_ident =
  match unfold t with
  | Vari v -> Pos.make pos (base_name v)
  | _ -> fatal pos "Not a variable of the proof context: %a." term t

(*let p_query_aux (c:config) (pos:popt) (s:sym) (ts:term list) :p_query_aux =
  match Hashtbl.find c s.sym_name, ts with
  | Q_compute, [_;t] ->
      P_query_normalize(p_term pos t,{strategy=SNF;steps=None})
  | Q_compute, _ -> assert false
  | _ -> assert false

let p_query (c:config) (pos:popt) (s:sym) (ts:term list) :p_query =
  Pos.make pos (p_query_aux c pos s ts)

let p_query_of_term (c:config) (pos:popt) (t:term) :p_query =
  match get_args t with
    | Symb s, ts -> p_query c pos s ts
    | _ -> fatal pos "Unhandled query expression: %a." term t*)

let p_term_of_string (pos:popt) (t:term): p_term =
  match t with
  | Symb s when String.is_string_literal s.sym_name ->
      begin
        let string = remove_quotes s.sym_name in
        let fname = match pos with Some{fname=Some fn;_} -> fn | _ -> "" in
        let stream = Parsing.Parser.Lp.parse_term_string fname string in
        try Stream.next stream with Stream.Failure -> assert false
      end
  | _ -> fatal pos "refine tactic not applied to a term string literal"

let p_rw_patt_of_string (pos:popt) (t:term): p_rw_patt option =
  match t with
  | Symb s when String.is_string_literal s.sym_name ->
      let string = remove_quotes s.sym_name in
      if string = "" then None
      else
        begin
          let fname = match pos with Some{fname=Some fn;_} -> fn | _ -> "" in
          let stream = Parsing.Parser.Lp.parse_rwpatt_string fname string in
          try Some (Stream.next stream) with Stream.Failure -> assert false
        end
  | _ -> fatal pos "rewrite tactic not applied to a pattern string literal"

let is_right (pos:popt) (t:term): bool =
  match t with
  | Symb s when String.is_string_literal s.sym_name ->
      begin
        match remove_quotes s.sym_name with
        | "left" -> false
        | "" | "right" -> true
        | _ ->
            fatal pos "rewrite tactic not applied to side string literal"
      end
  | _ -> fatal pos "rewrite tactic not applied to a side string literal"

(** [p_tactic t] interprets the term [t] as a tactic. *)
let p_tactic (ss:Sig_state.t) (pos:popt) :int StrMap.t -> term -> p_tactic =
  let c = get_config ss pos in
  let rec tac idmap t = Pos.make pos (tac_aux idmap t)
  and tac_aux idmap t =
    match get_args t with
    | Symb s, ts ->
        begin
          try
            match Hashtbl.find c s.sym_name, ts with
            | T_admit, _ -> P_tac_admit
            | T_and, [t1;t2] -> P_tac_and(tac idmap t1, tac idmap t2)
            | T_and, _ -> assert false
            | T_apply, [_;t] -> P_tac_apply(p_term pos idmap t)
            | T_apply, _ -> assert false
            | T_assume, [t] -> P_tac_assume [Some(p_ident_of_sym pos t)]
            | T_assume, _ -> assert false
            | T_fail, _ -> P_tac_fail
            | T_generalize, [_;t] -> P_tac_generalize(p_ident_of_var pos t)
            | T_generalize, _ -> assert false
            | T_have, [t1;t2] ->
                let prf_sym = Builtin.get ss pos "P" in
                let prf = p_term pos idmap (mk_Symb prf_sym) in
                let t2 = Pos.make pos (P_Appl(prf, p_term pos idmap t2)) in
                P_tac_have(p_ident_of_sym pos t1, t2)
            | T_have, _ -> assert false
            | T_induction, _ -> P_tac_induction
            | T_orelse, [t1;t2] -> P_tac_orelse(tac idmap t1, tac idmap t2)
            | T_orelse, _ -> assert false
            | T_refine, [t] -> P_tac_refine(p_term_of_string pos t)
            | T_refine, _ -> assert false
            | T_reflexivity, _ -> P_tac_refl
            | T_remove, [_;t] -> P_tac_remove [p_ident_of_var pos t]
            | T_remove, _ -> assert false
            | T_repeat, [t] -> P_tac_repeat(tac idmap t)
            | T_repeat, _ -> assert false
            | T_rewrite, [side;pat;_;t] ->
                P_tac_rewrite(is_right pos side,
                              p_rw_patt_of_string pos pat, p_term pos idmap t)
            | T_rewrite, _ -> assert false
            | T_set, [t1;_;t2] ->
                P_tac_set(p_ident_of_sym pos t1, p_term pos idmap t2)
            | T_set, _ -> assert false
            | T_simplify, _ -> P_tac_simpl SimpAll
            | T_simplify_beta, _ -> P_tac_simpl SimpBetaOnly
            | T_solve, _ -> P_tac_solve
            | T_symmetry, _ -> P_tac_sym
            | T_try, [t] -> P_tac_try(tac idmap t)
            | T_try, _ -> assert false
            | T_why3, _ -> P_tac_why3 None
          with Not_found ->
            fatal pos "Unhandled tactic expression: %a." term t
        end
    | _ -> fatal pos "Unhandled tactic expression: %a." term t
  in tac

(** [handle ss sym_pos prv ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. *)
let rec handle :
  Sig_state.t -> popt -> bool -> proof_state -> p_tactic -> proof_state =
  fun ss sym_pos prv ps ({elt;pos} as tac) ->
  if Logger.log_enabled () then log "%a" Pretty.tactic tac;
  match ps.proof_goals with
  | [] -> assert false (* done before *)
  | g::gs ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\""
  | P_tac_query _ -> assert false (* done before *)
  (* Tactics that apply to both unification and typing goals: *)
  | P_tac_simpl SimpAll ->
      {ps with proof_goals = Goal.simpl Eval.snf g :: gs}
  | P_tac_simpl SimpBetaOnly ->
      let tags = [`NoRw; `NoExpand] in
      {ps with proof_goals = Goal.simpl (Eval.snf ~tags) g :: gs}
  | P_tac_simpl (SimpSym qid) ->
      let s = Sig_state.find_sym ~prt:true ~prv:true ss qid in
      let g = Goal.simpl (fun _ctx -> Eval.unfold_sym s) g in
      {ps with proof_goals = g :: gs}
  | P_tac_solve -> tac_solve pos ps
  | _ ->
  (* Tactics that apply to typing goals only: *)
  match g with
  | Unif _ -> fatal pos "Not a typing goal."
  | Typ ({goal_hyps=env;_} as gt) ->
  let scope t = Scope.scope_term ~mok:(Proof.meta_of_key ps) prv ss env t in
  (* Function to apply the assume tactic several times without checking the
     validity of identifiers. *)
  let assume idopts =
    match idopts with
    | [] -> ps
    | _ -> tac_refine pos ps gt gs (new_problem())
             (scope (P.abst_list idopts P.wild))
  in
  (* Function for checking that an identifier is not already in use. *)
  let check id =
    if Env.mem id.elt env then fatal id.pos "Identifier already in use." in
  match elt with
  | P_tac_fail
  | P_tac_query _
  | P_tac_simpl _
  | P_tac_solve -> assert false (* done before *)
  | P_tac_admit -> tac_admit ss sym_pos ps gt
  | P_tac_apply pt ->
      let is_reduced = Stdlib.ref false in
      (* [ext_whnf] reduces a term to whnf and, if it is already in whnf,
         reduce also its subterms similarly. Records also whether there has
         been a reduction. *)
      let rec ext_whnf c t =
        if Logger.log_enabled() then log "ext_whnf %a" term t;
        match Eval.whnf_opt c t with
        | Some t' -> Stdlib.(is_reduced := true); t'
        | None ->
            match get_args t with
            | (Symb s) as h, ts when is_constant s ->
                add_args_map h (ext_whnf c) ts
            | _ -> t
      in
      (*let print_result s f arg x result =
        let r = f x in
          if Logger.log_enabled() then log "%s %a ≡ %a" s arg x result r;
          r
        in*)
      (*let ext_whnf c t =
        print_result "ext_whnf" (ext_whnf c) term t term in*)
      (* [top_ext_whnf] reduces a term to whnf and, if it is already in
         whnf and of the form [Appl(_,u)], then reduces [u] according to
         [ext_whnf]. Records also whether there has been a reduction. *)
      let top_ext_whnf c t =
        if Logger.log_enabled() then log "top_ext_whnf %a" term t;
        match Eval.whnf_opt c t with
        | Some t' -> Stdlib.(is_reduced := true); t'
        | None ->
            match unfold t with
            | Appl(pi,u) -> mk_Appl(pi,ext_whnf c u)
            | _ -> t
      in
      (*let top_ext_whnf c t =
        print_result "top_ext_whnf" (top_ext_whnf c) term t term in*)
      let top_ext_whnf_opt c t =
        if Logger.log_enabled() then log "top_ext_whnf_opt %a" term t;
        Stdlib.(is_reduced := false);
        let t' = top_ext_whnf c t in
        if Stdlib.(!is_reduced) then Some t' else None
      in
      (*let top_ext_whnf_opt c t =
        print_result "top_ext_whnf_opt"
          (top_ext_whnf_opt c) term t (D.option term) in*)
      (* Try to find [k >= 0] such that [lem] reduces to [Π x1:A1, .., Π
         xk:Ak, B] and [B] matches [goal]. *)
      let rec find goal k xs lem is_whnf_lem =
        if Logger.log_enabled() then
          log "find %d %a %b\nmatching %a"
            k term lem is_whnf_lem term goal;
        let t0 = Time.save() in
        match Rewrite.matching_subs (xs,lem) goal with
        | Some _ -> Some k
        | None ->
            Time.restore t0;
            match unfold lem with
            | Prod(_,b) ->
                let x,lem' = unbind ~name:("$"^binder_name b) b in
                find goal (k+1) (Array.append xs [|x|]) lem' false
            | _ ->
                if is_whnf_lem then None
                else
                  match top_ext_whnf_opt [] lem with
                  | None -> None
                  | Some lem' -> find goal k xs lem' true
      in
      begin
        let t = scope pt in
        let c = Env.to_ctxt env in
        if let p = new_problem() in
           Infer.check_noexn p c t gt.goal_type <> None
           && Unif.solve_noexn p && Timed.(!p).unsolved = []
        then
          let p = new_problem() in
          tac_refine pos ps gt gs p t
        else
          let a =
            let p = new_problem() in
            match Infer.infer_noexn p c t with
            | None ->
                let ids = Ctxt.names c in
                let term = term_in ids in
                fatal pos "[%a] is not typable." term t
            | Some (_, a) -> a
          in
          let r =
            let t0 = Time.save () in
            match find gt.goal_type 0 [||] a false with
            | Some _ as r -> r
            | None ->
                Time.restore t0;
                match top_ext_whnf_opt c gt.goal_type with
                | None -> None
                | Some u -> find u 0 [||] a false
          in
          match r with
          | Some k ->
              let t = scope (P.appl_wild pt k) in
              let p = new_problem() in
              tac_refine pos ps gt gs p t
          | None ->
              fatal pos "Could not find a subterm of [%a] or of its whnf \
                         matching the current goal or its whnf. \
                         Try refine instead." term a
      end
  | P_tac_assume idopts ->
      (* Check that no idopt is None. *)
      if List.exists ((=) None) idopts then
        fatal pos "underscores not allowed in assume";
      (* Check that the given identifiers are not already used. *)
      List.iter (Option.iter check) idopts;
      (* Check that the given identifiers are pairwise distinct. *)
      Syntax.check_distinct_idopts idopts;
      assume idopts
  | P_tac_generalize {elt=id; pos=idpos} ->
      (* From a goal [e1,id:a,e2 ⊢ ?[e1,id,e2] : u], generate a new goal [e1 ⊢
         ?m[e1] : Π id:a, Π e2, u], and refine [?[e]] with [?m[e1] id e2]. *)
      begin
        try
          let p = new_problem() in
          let e2, x, e1 = List.split (fun (s,_) -> s = id) env in
          let u = gt.goal_type in
          let q = Env.to_prod [x] (Env.to_prod e2 u) in
          let m = LibMeta.fresh p (Env.to_prod e1 q) (List.length e1) in
          let me1 = mk_Meta (m, Env.to_terms e1) in
          let t =
            List.fold_left (fun t (_,(v,_,_)) -> mk_Appl(t, mk_Vari v))
              me1 (x :: List.rev e2)
          in
          tac_refine pos ps gt gs p t
        with Not_found -> fatal idpos "Unknown hypothesis %a" uid id;
      end
  | P_tac_have(id, t) ->
      (* From a goal [e ⊢ ?[e] : u], generate two new goals [e ⊢ ?1[e] : t]
         and [e,x:t ⊢ ?2[e,x] : u], and refine [?[e]] with [?2[e,?1[e]]. *)
      check id;
      let p = new_problem() in
      let t = scope t in
      (* Generate the constraints for [t] to be of type [Type]. *)
      let c = Env.to_ctxt env in
      begin
        match Infer.check_noexn p c t mk_Type with
        | None ->
            let ids = Ctxt.names c in let term = term_in ids in
            fatal pos "%a is not of type Type." term t
        | Some t ->
        (* Create a new goal of type [t]. *)
        let n = List.length env in
        let m1 = LibMeta.fresh p (Env.to_prod env t) n in
        (* Refine the focused goal. *)
        let v = new_var id.elt in
        let env' = Env.add id.elt v t None env in
        let m2 = LibMeta.fresh p (Env.to_prod env' gt.goal_type) (n+1) in
        let ts = Env.to_terms env in
        let u = mk_Meta (m2, Array.append ts [|mk_Meta (m1, ts)|]) in
        tac_refine pos ps gt gs p u
      end
  | P_tac_set(id,t) ->
      (* From a goal [e ⊢ ?[e]:a], generate a new goal [e,x:b≔t ⊢ ?1[e,x]:a],
         where [b] is the type of [t], and refine [?[e]] with [?1[e,t]]. *)
      check id;
      let p = new_problem() in
      let t = scope t in
      let c = Env.to_ctxt env in
      begin
        match Infer.infer_noexn p c t with
        | None ->
            let ids = Ctxt.names c in let term = term_in ids in
            fatal pos "%a is not typable." term t
        | Some (t,b) ->
            if Unif.solve_noexn p then begin
              let x = new_var id.elt in
              let e' = Env.add id.elt x b (Some t) env in
              let n = List.length e' in
              let v = LibTerm.fold x t gt.goal_type in
              let m = LibMeta.fresh (new_problem()) (Env.to_prod e' v) n in
              let ts = Env.to_terms env in
              let u = mk_Meta (m, Array.append ts [|t|]) in
              (*tac_refine pos ps gt gs p u*)
              LibMeta.set p gt.goal_meta (bind_mvar (Env.vars env) u);
              (*let g = Goal.of_meta m in*)
              let g = Typ {goal_meta=m; goal_hyps=e'; goal_type=v} in
              {ps with proof_goals = g :: Proof.add_goals_of_problem p gs}
            end else fatal pos "The unification constraints for %a \
                            to be typable are not satisfiable." term t
      end
  | P_tac_induction -> tac_induction pos ps gt gs
  | P_tac_refine t -> tac_refine pos ps gt gs (new_problem()) (scope t)
  | P_tac_refl ->
      begin
        let cfg = Rewrite.get_eq_config ss pos in
        let _,vs = Rewrite.get_eq_data cfg pos gt.goal_type in
        let idopts = Env.gen_valid_idopts env (List.map base_name vs) in
        let ps = assume idopts in
        match ps.proof_goals with
        | [] -> assert false
        | Unif _::_ -> assert false
        | Typ gt::gs ->
            let cfg = Rewrite.get_eq_config ss pos in
            let (a,l,_),_ = Rewrite.get_eq_data cfg pos gt.goal_type in
            let prf = add_args (mk_Symb cfg.symb_refl) [a; l] in
            tac_refine pos ps gt gs (new_problem()) prf
      end
  | P_tac_remove ids ->
      (* Remove hypothesis [id] in goal [g]. *)
      let remove g id =
        match g with
        | Unif _ -> assert false
        | Typ gt ->
            let k =
              try List.pos (fun (s,_) -> s = id.elt) env
              with Not_found -> fatal id.pos "Unknown hypothesis."
            in
            let m = gt.goal_meta in
            let n = m.meta_arity - 1 in
            let a = cleanup !(m.meta_type) in (* cleanup necessary *)
            (* a = Π x0:A0, .., Π xn-1:An-1, B *)
            (* [codom_binder i a] returns the binder [xi:Ai --> Π xi+1:Ai+1,
               .., Π xn-1:An-1, B] with [x0,..,xi-1] replaced by
               [mk_Kind]. This replacement does not matter here because we are
               only interested in knowing whether [xi] occurs in [Π xi+1:Ai+1,
               .., Π xn-1:An-1, B]. *)
            let rec codom_binder i a =
              match unfold a with
              | Prod(_,b) ->
                  if i <= 0 then b else codom_binder (i-1) (subst b mk_Kind)
              | LLet(_,t,b) ->
                  if i <= 0 then b else codom_binder (i-1) (subst b t)
              | _ -> assert false
            in
            (* Because [env] is in reverse order compared to [a], we have [env
               = [xn-1; ..; x0]] and the position [k] corresponds to
               [xn-k]. *)
            if binder_occur (codom_binder (n - k) a) then
              fatal id.pos "%s cannot be removed because of dependencies."
                id.elt;
            let env' = List.filter (fun (s,_) -> s <> id.elt) env in
            let a' = Env.to_prod env' gt.goal_type in
            let p = new_problem() in
            let m' = LibMeta.fresh p a' n in
            let t = mk_Meta(m',Env.to_terms env') in
            LibMeta.set p m (bind_mvar (Env.vars env) t);
            Goal.of_meta m'
      in
      Syntax.check_distinct ids;
      (* Reorder [ids] wrt their positions. *)
      let n = gt.goal_meta.meta_arity - 1 in
      let id_pos id =
        try id, n - List.pos (fun (s,_) -> s = id.elt) env
        with Not_found -> fatal id.pos "Unknown hypothesis."
      in
      let cmp (_,k1) (_,k2) = Stdlib.compare k2 k1 in
      let ids = List.map fst (List.sort cmp (List.map id_pos ids)) in
      let g = List.fold_left remove g ids in
      {ps with proof_goals = g::gs}
  | P_tac_rewrite(l2r,pat,eq) ->
      let pat = Option.map (Scope.scope_rw_patt ss env) pat in
      let p = new_problem() in
      tac_refine pos ps gt gs p
        (Rewrite.rewrite ss p pos gt l2r pat (scope eq))
  | P_tac_sym ->
      let cfg = Rewrite.get_eq_config ss pos in
      let (a,l,r),_ = Rewrite.get_eq_data cfg pos gt.goal_type in
      let p = new_problem() in
      let prf =
        let mt = mk_Appl(mk_Symb cfg.symb_P,
                         add_args (mk_Symb cfg.symb_eq) [a;r;l]) in
        let meta_term = LibMeta.make p (Env.to_ctxt env) mt in
        (* The proofterm is [eqind a r l M (λx,eq a l x) (refl a l)]. *)
        Rewrite.swap cfg a r l meta_term
      in
      tac_refine pos ps gt gs p prf
  | P_tac_why3 cfg ->
      begin
        let ids = get_prod_ids env false gt.goal_type in
        let idopts = Env.gen_valid_idopts env ids in
        let ps = assume idopts in
        match ps.proof_goals with
        | Typ gt::_ ->
            Why3_tactic.handle ss pos cfg gt; tac_admit ss sym_pos ps gt
        | _ -> assert false
      end
  | P_tac_try tactic ->
      begin
        try handle ss sym_pos prv ps tactic
        with Fatal(_, _s) -> ps
      end
  | P_tac_orelse(t1,t2) ->
      begin
        try handle ss sym_pos prv ps t1
        with Fatal(_, _s) -> handle ss sym_pos prv ps t2
      end
  | P_tac_repeat t ->
      begin
        try
          let nb_goals = List.length ps.proof_goals in
          let ps = handle ss sym_pos prv ps t in
          if List.length ps.proof_goals < nb_goals then ps
          else handle ss sym_pos prv ps tac
        with Fatal(_, _s) -> ps
      end
  | P_tac_and(t1,t2) ->
      let ps = handle ss sym_pos prv ps t1 in
      handle ss sym_pos prv ps t2
  | P_tac_eval pt ->
      let t = Eval.snf (Env.to_ctxt env) (scope pt) in
      let idmap = get_names g in
      handle ss sym_pos prv ps (p_tactic ss pos idmap t)

(** Representation of a tactic output. *)
type tac_output = proof_state * Query.result

(** [handle ss sym_pos prv ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. *)
let handle :
  Sig_state.t -> popt -> bool -> proof_state -> p_tactic -> tac_output =
  fun ss sym_pos prv ps ({elt;pos} as tac) ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\""
  | P_tac_query(q) ->
    if Logger.log_enabled () then log "%a@." Pretty.tactic tac;
    ps, Query.handle ss (Some ps) q
  | _ ->
  match ps.proof_goals with
  | [] -> fatal pos "No remaining goals."
  | g::_ ->
    if Logger.log_enabled() then
      log ("%a@\n" ^^ Color.red "%a")
        Proof.Goal.pp_no_hyp g Pretty.tactic tac;
    handle ss sym_pos prv ps tac, None

(** [handle sym_pos prv r tac n] applies the tactic [tac] from the previous
   tactic output [r] and checks that the number of goals of the new proof
   state is compatible with the number [n] of subproofs. *)
let handle :
  Sig_state.t -> popt -> bool -> tac_output -> p_tactic -> int -> tac_output =
  fun ss sym_pos prv (ps, _) t nb_subproofs ->
  let (ps', _) as a = handle ss sym_pos prv ps t in
  let nb_goals_before = List.length ps.proof_goals in
  let nb_goals_after = List.length ps'.proof_goals in
  let nb_newgoals = nb_goals_after - nb_goals_before in
  if nb_newgoals <= 0 then
    if nb_subproofs = 0 then a
    else fatal t.pos "A subproof is given but there is no subgoal."
  else if is_destructive t then
    match nb_newgoals + 1 - nb_subproofs with
    | 0 -> a
    | n when n > 0 ->
      fatal t.pos "Missing subproofs (%d subproofs for %d subgoals):@.%a"
        nb_subproofs (nb_newgoals + 1) goals ps'
    | _ ->
      fatal t.pos "Too many subproofs (%d subproofs for %d subgoals):@.%a"
        nb_subproofs (nb_newgoals + 1) goals ps'
  else match nb_newgoals - nb_subproofs with
    | 0 -> a
    | n when n > 0 ->
      fatal t.pos "Missing subproofs (%d subproofs for %d subgoals):@.%a"
        nb_subproofs nb_newgoals goals ps'
    | _ -> fatal t.pos "Too many subproofs (%d subproofs for %d subgoals)."
             nb_subproofs nb_newgoals
