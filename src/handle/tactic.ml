(** Handling of tactics. *)

open Lplib open Extra
open Common open Error open Pos
open Parsing open Syntax
open Core open Term open Print
open Proof
open Timed
open Goal

(** Logging function for tactics. *)
let log = Logger.make 't' "tact" "tactics"
let log = log.pp

(** Number of admitted axioms in the current signature. Used to name the
    generated axioms. This reference is reset in {!module:Compile} for each
    new compiled module. *)
let admitted_initial_value = min_int
let admitted : int Stdlib.ref = Stdlib.ref admitted_initial_value
let reset_admitted() =
  Stdlib.(let a = !admitted in admitted := admitted_initial_value; a)
let restore_admitted (a:int) = Stdlib.(admitted := a)

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
    wrn sym_pos "axiom %a: %a" uid name term !(m.meta_type);
    (* Temporary hack for axioms to have a declaration position in the order
       they are created, and strictly before the symbol. *)
    (* FIXME: use sym_decl_pos instead ? *)
    let id = {elt=name; pos=sym_pos} in
    let pos = shift Stdlib.(!admitted) sym_pos in
    (* We ignore the new ss returned by Sig_state.add_symbol: axioms do not
       need to be in scope. *)
    snd (Sig_state.add_symbol ss
           Public Defin Eager true id pos !(m.meta_type) [] None)
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
    | Typ gt -> !(gt.goal_meta.meta_value) = None
    | _ -> false
  in
  let gs_typ = List.filter non_instantiated gs_typ in
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
let _ = log "SOLVE: %a" (List.pp Goal.pp "\n") proof_goals in
  {ps with proof_goals}

(** [tac_refine pos ps gt gs p t] refines the typing goal [gt] with [t]. *)
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
    log (Color.gre "%a ≔ %a") meta gt.goal_meta term t;
  LibMeta.set p gt.goal_meta (bind_mvar (Env.vars gt.goal_hyps) t);
  (* Convert the metas and constraints of [p] not in [gs] into new goals. *)
  tac_solve pos {ps with proof_goals = add_goals_of_problem p gs}

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
  | T_all_hyps
  | T_apply
  | T_assume
  | T_assumption
  | T_change
  | T_compose
  | T_fail
  | T_first_hyp
  | T_focus
  | T_generalize
  | T_have
  | T_induction
  | T_orelse
  | T_print
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
  let add n v =
    let s = Builtin.get ss pos [] n in
    Hashtbl.add t s.sym_name v
  in
  add "admit" T_admit;
  add "all_hyps" T_all_hyps;
  add "apply" T_apply;
  add "assume" T_assume;
  add "assumption" T_assumption;
  add "change" T_change;
  add "compose" T_compose;
  add "fail" T_fail;
  add "first_hyp" T_first_hyp;
  add "focus" T_focus;
  add "generalize" T_generalize;
  add "have" T_have;
  add "induction" T_induction;
  add "orelse" T_orelse;
  add "print" T_print;
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
let p_term (ss:Sig_state.t) (pos:popt): int StrMap.t -> term -> p_term =
  let rec term idmap (t:term) :p_term = Pos.make pos (term_aux idmap t)
  and params idmap x a =
    [Some(Pos.make pos (base_name x))],Some(term idmap a),false
  and term_aux idmap t :p_term_aux =
    match unfold t with
    | Type -> P_Type
    | Symb s ->
      let mp = if StrMap.mem s.sym_name ss.in_scope then [] else s.sym_path in
      let expl = s.sym_impl <> [] in
      let t = P_Iden(Pos.make pos (mp,s.sym_name),expl) in
      if !(s.sym_nota) = NoNotation then t else P_Wrap (Pos.make pos t)
    | Vari v -> P_Iden(Pos.make pos ([],base_name v),false)
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
    | Meta _ -> P_Wild
    | _ -> fatal pos "Unhandled term expression: %a." Print.term t
  in term

(** [string_of_term pos t] returns the string contained in a string literal
    term [t]. *)
let string_of_term : popt -> term -> string = fun pos t ->
  match unfold t with
  | Symb s when String.is_string_literal s.sym_name ->
      String.remove_quotes s.sym_name
  | _ -> fatal pos "not a string literal: %a" term t

let p_ident_of_var (pos:popt) (t:term) :p_ident =
  match unfold t with
  | Vari v -> Pos.make pos (base_name v)
  | _ -> fatal pos "Not a variable of the proof context: %a." term t

(* [pos_of_string s] assumes that [s] is a string literal and returns the
   lexing position of the content of [s]. *)
let pos_of_string: sym -> Lexing.position =
  let f p = {p with start_offset=p.start_offset+1; start_col=p.start_col+1;
                    end_offset=p.end_offset-1; end_col=p.end_col-1} in
  fun s -> lexing_opt (Option.map f s.sym_pos)

(** [p_term_of_string_term pos t] turns into a p_term a string literal term
    [t] that is part of a bigger term obtained by scoping and normalizing of a
    p_term at position [pos]. *)
let p_term_of_string_term (pos:popt) (t:term): p_term =
  match t with
  | Symb s when String.is_string_literal s.sym_name ->
    Parsing.Parser.Lp.parse_term_string (pos_of_string s)
      (String.remove_quotes s.sym_name)
  | _ -> fatal pos "not a string literal"

(** [p_rwpatt_of_string_term pos t] turns into a p_rwpatt option a string
    literal term [t] that is part of a bigger term obtained by scoping and
    normalizing of a p_term at position [pos]. *)
let p_rwpatt_of_string_term (pos:popt) (t:term): p_rwpatt option =
  (*if Logger.log_enabled() then
    log "p_rwpatt_of_string_term %a %a" Pos.short pos term t;*)
  match t with
  | Symb s when String.is_string_literal s.sym_name ->
      let string = String.remove_quotes s.sym_name in
      if string = "" then None else
        Some (Parsing.Parser.Lp.parse_rwpatt_string (pos_of_string s) string)
  | _ -> fatal pos "not a string literal"

(** [int_of_term pos t] returns the int contained in a string literal
    term [t]. *)
let int_of_term : popt -> term -> int = fun pos t ->
  try int_of_string (string_of_term pos t)
  with Failure _ -> fatal pos "too big integer"

(** [is_right pos t] returns [true] iff [t] is ["right"]. *)
let is_right (pos:popt) (t:term): bool =
  match string_of_term pos t with
  | "left" -> false
  | "" | "right" -> true
  | _ -> fatal pos "invalid side literal"

(** [new_name prefix env] returns a string prefixed by [prefix] and not
    occurring in [env]. *)
let new_name (prefix:string) (env:Env.t): string =
  if Env.mem prefix env then
    let i = ref 0 in
    let new_name() = prefix ^ string_of_int !i in
    let s = ref (new_name()) in
    while Env.mem !s env do incr i; s := new_name() done;
    !s
  else prefix

(** [handle ss sym_pos priv ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. *)
let handle (ss:Sig_state.t) (sym_pos:popt) (priv:bool)
    :proof_state -> p_tactic -> proof_state =

  let rec progress (ps:proof_state) (ptac: p_tactic): proof_state option =
    try let new_ps = handle ps ptac in
      if List.length new_ps.proof_goals < List.length ps.proof_goals
      then Some new_ps
      else None
    with Fatal _ -> None

  (* [p_tactic ss g env pos t] weak head normalizes [t] and converts the
     result into a p_tactic. *)
  and p_tactic (ps:proof_state) (g:goal) (env:Env.t) (pos:Pos.popt)
    : term -> proof_state * p_tactic =
    let idmap = get_names g
    and ctx = Env.to_ctxt env in
    let p_term = p_term ss pos idmap in
    let mk = Pos.make pos in
    let tac_eval t = mk(P_tac_eval(p_term t)) in
    fun t ->
      let t = Eval.whnf ctx t in
      if Logger.log_enabled() then log "reduces to: %a" term t;
      match get_args t with
      | Symb s, ts ->
        begin
          try
            (*FIXME: compute config only once in a proof*)
            let c = get_config ss pos in
            match Hashtbl.find c s.sym_name, ts with
            | T_admit, _ -> ps, mk P_tac_admit
            | T_all_hyps, [t] -> ps, mk(P_tac_all_hyps(p_term t))
            | T_all_hyps, _ -> assert false
            | T_apply, [_;_;t] -> ps, mk(P_tac_apply(p_term t))
            | T_apply, _ -> assert false
            | T_assume, [prefix;_;_;Abst(_, t)] ->
              begin
                let n = new_name (string_of_term pos prefix) env in
                let idopts = [Some(Pos.make pos n)] in
                let new_ps = handle ps (mk (P_tac_assume idopts)) in
                match new_ps.proof_goals with
                | Typ{goal_hyps=(_,(v,_,_))::_;_}::_ ->
                  new_ps, mk(P_tac_eval(p_term(subst t (mk_Vari v))))
                | _ -> assert false
              end
            | T_assume, _ -> assert false
            | T_assumption, [] -> ps, mk P_tac_assumption
            | T_assumption, _ -> assert false
            | T_change, [_;_;t] -> ps, mk(P_tac_change (p_term t))
            | T_change, _ -> assert false
            | T_compose, [t1;t2] ->
              let ps = handle ps (tac_eval t1) in ps, tac_eval t2
            | T_compose, _ -> assert false
            | T_fail, _ -> ps, mk P_tac_fail
            | T_first_hyp, [t] -> ps, mk(P_tac_first_hyp(p_term t))
            | T_first_hyp, _ -> assert false
            | T_focus, [t] -> ps, mk(P_tac_focus(string_of_term pos t))
            | T_focus, _ -> assert false
            | T_generalize, [_;_;t] ->
              ps, mk(P_tac_generalize(p_ident_of_var pos t))
            | T_generalize, _ -> assert false
            | T_have, [t1;_;_;t2] ->
                let prf_sym = Builtin.get ss pos [] "P" in
                let prf = p_term (mk_Symb prf_sym) in
                let t2 = Pos.make pos (P_Appl(prf, p_term t2)) in
                ps, mk(P_tac_have(Pos.make pos (string_of_term pos t1), t2))
            | T_have, _ -> assert false
            | T_induction, _ -> ps, mk P_tac_induction
            | T_orelse, [t1;t2] ->
              ps, mk(P_tac_orelse(tac_eval t1, tac_eval t2))
            | T_orelse, _ -> assert false
            | T_print, [t] ->
              let arg =
                match unfold t with
                | Symb s ->
                  let n = s.sym_name in
                  if String.is_string_literal n then
                    let n = String.remove_quotes n in
                    if n = "" then Goal else String n
                  else Symbol(Pos.make pos (s.sym_path, n))
                | _ -> fatal pos "not a symbol or string literal: %a" term t
              in
              ps, mk(P_tac_query (Pos.make pos (P_query_print arg)))
            | T_print, _ -> assert false
            | T_refine, [t] ->
              ps, mk(P_tac_refine(p_term_of_string_term pos t))
            | T_refine, _ -> assert false
            | T_reflexivity, _ -> ps, mk P_tac_refl
            | T_remove, [_;_;t] -> ps, mk(P_tac_remove [p_ident_of_var pos t])
            | T_remove, _ -> assert false
            | T_repeat, [t] -> ps, mk(P_tac_repeat(tac_eval t))
            | T_repeat, _ -> assert false
            | T_rewrite, [side;pat;_;_;t] ->
              ps, mk(P_tac_rewrite(is_right pos side,
                                   p_rwpatt_of_string_term pos pat, p_term t))
            | T_rewrite, _ -> assert false
            | T_set, [t1;_;_;t2] ->
              let n = string_of_term pos t1 in
              ps, mk(P_tac_set(Pos.make pos n, p_term t2))
            | T_set, _ -> assert false
            | T_simplify, _ -> ps, mk(P_tac_simpl SimpAll)
            | T_simplify_beta, _ -> ps, mk(P_tac_simpl SimpBetaOnly)
            | T_solve, _ -> ps, mk P_tac_solve
            | T_symmetry, _ -> ps, mk P_tac_sym
            | T_try, [t] -> ps, mk(P_tac_try(tac_eval t))
            | T_try, _ -> assert false
            | T_why3, _ -> ps, mk(P_tac_why3 None)
          with Not_found ->
            fatal pos "Unhandled tactic expression: %a." term t
        end
      | _ -> fatal pos "Unhandled tactic expression: %a." term t

  and handle ps ({elt;pos} as tac) =
  if Logger.log_enabled() then log "%a" Pretty.tactic tac;
  match ps.proof_goals with
  | [] -> assert false (* done before *)
  | g::gs ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\""
  | P_tac_query q -> let _ = Query.handle ss (Some ps) q in ps
  (* Tactics that apply to both unification and typing goals: *)
  | P_tac_simpl SimpAll ->
      begin
        match Goal.simpl_opt Eval.snf_opt g with
        | Some g -> {ps with proof_goals = g :: gs}
        | None -> fatal pos "Could not simplify the goal."
      end
  | P_tac_simpl SimpBetaOnly ->
      begin
        match Goal.simpl_opt (Eval.snf_opt ~tags:[NoRw;NoExpand]) g with
        | Some g -> {ps with proof_goals = g :: gs}
        | None -> fatal pos "Could not simplify the goal."
      end
  | P_tac_simpl (SimpSym qid) ->
      begin
        let s = Sig_state.find_sym ~prt:true ~prv:true ss qid in
        match Goal.simpl_opt (fun _ctx -> Eval.unfold_sym_opt s) g with
        | Some g -> {ps with proof_goals = g :: gs}
        | None -> fatal pos "Could not simplify the goal."
      end
  | P_tac_solve -> tac_solve pos ps
  | P_tac_focus n ->
      let n = int_of_string n in
      if n < 2 || n > List.length ps.proof_goals then
        fatal pos "focus index out of bound"
      else {ps with proof_goals = List.move_nth (n-1) ps.proof_goals}
  | _ ->
  (* Tactics that apply to typing goals only: *)
  match g with
  | Unif _ -> fatal pos "Not a typing goal."
  | Typ ({goal_hyps=env;_} as gt) ->
  let scope ?(prot=false) =
    let find_sym: Sig_state.find_sym =
      fun ~prt:_ ~prv:_ -> Sig_state.find_sym ~prt:prot ~prv:priv in
    Scope.scope_term ~find_sym ~mok:(Proof.meta_of_key ps) priv ss env
  in
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
  | P_tac_solve
  | P_tac_focus _ -> assert false (* done before *)
  | P_tac_admit -> tac_admit ss sym_pos ps gt
  | P_tac_all_hyps t ->
    let t = scope t in
    let l = mk_Symb (Builtin.get ss pos [] "Level") in
    let try_assumption (ps: proof_state) (_,(v,a,_)): proof_state =
      match ps.proof_goals with
      | [] -> fatal pos "all_hyps called on empty goal list."
      | g :: _ ->
        let p = new_problem() in
        let m = mk_Meta(LibMeta.fresh p l 0,[||]) in
        let t = mk_Appl(mk_Appl(mk_Appl(t,m),a),mk_Vari v) in
        try let ps, t = p_tactic ps g env pos t in handle ps t
        with Fatal _ -> ps
    in
    let ps' = List.fold_left try_assumption ps gt.goal_hyps in
    if ps' == ps then
      fatal pos "(all_hyps %a) fails on all assumptions." term t
    else ps'
  | P_tac_apply pt ->
      let t = scope pt in
      (* Compute the product arity of the type of [t]. *)
      let n =
        let c = Env.to_ctxt env in
        let p = new_problem () in
        match Infer.infer_noexn p c t with
        | None ->
            let ids = Ctxt.names c in let term = term_in ids in
            fatal pos "(%a) is not typable." term t
        | Some (_, a) -> LibTerm.count_products Eval.whnf c a
      in
      let t = scope (P.appl_wild pt n) in
      tac_refine pos ps gt gs (new_problem()) t
  | P_tac_assume idopts ->
      (* Check that no idopt is None. *)
      if List.exists ((=) None) idopts then
        fatal pos "Underscores not allowed in assume.";
      (* Check that the given identifiers are not already used. *)
      List.iter (Option.iter check) idopts;
      (* Check that the given identifiers are pairwise distinct. *)
      Syntax.check_distinct_idopts idopts;
      assume idopts
  | P_tac_change pa ->
      let vname = "x" in
      let vabs = Pos.make pos vname in
      let varg = Pos.make pos ([],vname) in
      let vparam = [[Some vabs],Some pa,false] in
      let idbody = Pos.make pos (P_Iden(varg,false)) in
      let id =  Pos.make pos (P_Abst(vparam,idbody)) in
      let pt = Pos.make pos (P_Appl(id,Pos.make pos P_Wild)) in
      tac_refine pos ps gt gs (new_problem()) (scope pt)
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
        with Not_found -> fatal idpos "Unknown hypothesis %a." uid id;
      end
  | P_tac_first_hyp pt ->
    let t = scope pt in
    let l = mk_Symb (Builtin.get ss pos [] "Level") in
    let f (_,(v,a,_)) =
      let p = new_problem() in
      let m = mk_Meta(LibMeta.fresh p l 0,[||]) in
      let t = mk_Appl(mk_Appl(mk_Appl(t,m),a),mk_Vari v) in
      let ps, t = p_tactic ps g env pos t in progress ps t
    in
    begin match List.find_map f gt.goal_hyps with
    | None -> fatal pos "(first_hyp %a) fails on all assumptions." term t
    | Some new_ps -> new_ps
    end
  | P_tac_have(id, pt) ->
      (* From a goal [e ⊢ ?[e] : u], generate two new goals [e ⊢ ?1[e] : t]
         and [e,x:t ⊢ ?2[e,x] : u], and refine [?[e]] with [?2[e,?1[e]]. *)
      check id;
      let p = new_problem() in
      let t = scope pt in
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
  | P_tac_assumption ->
    let idmap = get_names g in
    let f (_,(v,_,_)) =
      let v = p_term ss pos idmap (mk_Vari v) in
      progress ps (Pos.make pos (P_tac_apply v))
    in
    begin match List.find_map f gt.goal_hyps with
      | None -> fatal pos "tactic assumption failed"
      | Some ps -> ps
    end
  | P_tac_set(id,pt) ->
      (* From a goal [e ⊢ ?[e]:a], generate a new goal [e,x:b≔t ⊢ ?1[e,x]:a],
         where [b] is the type of [t], and refine [?[e]] with [?1[e,t]]. *)
      check id;
      let p = new_problem() in
      let t = scope pt in
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
              LibMeta.set p gt.goal_meta (bind_mvar (Env.vars env) u);
              let g = Typ {goal_meta=m; goal_hyps=e'; goal_type=v} in
              {ps with proof_goals = g :: add_goals_of_problem p gs}
            end else fatal pos "The unification constraints for %a \
                            to be typable are not satisfiable." term t
      end
  | P_tac_induction -> tac_induction pos ps gt gs
  | P_tac_refine pt -> tac_refine pos ps gt gs (new_problem()) (scope pt)
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
      let pat = Option.map (Scope.scope_rwpatt ss env) pat in
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
  | P_tac_try t ->
      begin try handle ps t with Fatal _ -> ps end
  | P_tac_orelse(t1,t2) ->
      begin try handle ps t1 with Fatal _ -> handle ps t2 end
  | P_tac_repeat t ->
      begin try
        let new_ps = handle ps t in
        if List.length new_ps.proof_goals < List.length ps.proof_goals
        then new_ps
        else handle new_ps tac
        with Fatal _ -> ps
      end
  | P_tac_and(t1,t2) -> handle (handle ps t1) t2
  | P_tac_eval pt ->
      let t = scope pt
      and p = new_problem()
      and c = Env.to_ctxt env in
      match Infer.infer_noexn p c t with
      | None ->
          let term = term_in (Ctxt.names c) in
          fatal pt.pos "Cannot infer the type of [%a]" term t
      | Some(t,_) ->
        if Unif.solve_noexn p && !p.unsolved = [] then
          let ps, t = p_tactic ps g env pos t in handle ps t
        else fatal pos "Cannot solve typing constraints for [%a]" term t

  in handle

(** Representation of a tactic output. *)
type tac_output = proof_state * Query.result

(** [handle ss sym_pos priv ps tac] applies tactic [tac] in the proof state
   [ps] and returns the new proof state. *)
let handle :
  Sig_state.t -> popt -> bool -> proof_state -> p_tactic -> tac_output =
  fun ss sym_pos priv ps ({elt;pos} as tac) ->
  match elt with
  | P_tac_fail -> fatal pos "Call to tactic \"fail\"."
  | P_tac_query(q) ->
    if Logger.log_enabled () then log "%a" Pretty.tactic tac;
    ps, Query.handle ss (Some ps) q
  | _ ->
  match ps.proof_goals with
  | [] -> fatal pos "No remaining goal."
  | g::_ ->
    if Logger.log_enabled() then log ("goal %a") Goal.pp_no_hyp g;
    handle ss sym_pos priv ps tac, None

(** [handle sym_pos priv r tac n] applies the tactic [tac] from the previous
   tactic output [r] and checks that the number of goals of the new proof
   state is compatible with the number [n] of subproofs. When [tac] fails,
   the proof state it was applied to is attached to the error (see
   {!val:Proof.state_on_error}). *)
let handle :
  Sig_state.t -> popt -> bool -> tac_output -> p_tactic -> int -> tac_output =
  fun ss sym_pos priv (ps, _) t nb_subproofs ->
  (* Attach the proof state [t] was applied to, to any error escaping its
     application. Errors raised inside tacticals like [try] or [orelse] are
     caught below this point, so only failures actually reported to the user
     are concerned. *)
  let (ps', _) as a =
    try handle ss sym_pos priv ps t
    with Fatal(p, msg, desc)
      when Stdlib.(!state_on_error) && ps.proof_goals <> [] ->
        let state = error_state ps in
        let desc = if desc = "" then state else desc ^ "\n" ^ state in
        raise (Fatal(p, msg, desc))
  in
  let nb_goals_before = List.length ps.proof_goals in
  let nb_goals_after = List.length ps'.proof_goals in
  let nb_newgoals = nb_goals_after - nb_goals_before in
  (* [t] ran, but the number of subproofs given does not match the number of
     subgoals it produced: report the proof state before and after its
     application. *)
  let mismatch : string -> 'a = fun reason ->
    fatal t.pos ~err_desc:(error_state ~after:ps' ps) "%s" reason in
  if nb_newgoals <= 0 then
    if nb_subproofs = 0 then a
    else mismatch "A subproof is given but there is no subgoal."
  else if is_destructive t then
    (match nb_newgoals + 1 - nb_subproofs with
    | 0 -> a
    | n when n > 0 ->
      mismatch (Printf.sprintf
        "Missing subproofs (%d subproofs for %d subgoals)."
        nb_subproofs (nb_newgoals + 1))
    | _ ->
      mismatch (Printf.sprintf
        "Too many subproofs (%d subproofs for %d subgoals)."
        nb_subproofs (nb_newgoals + 1)))
  else match nb_newgoals - nb_subproofs with
    | 0 -> a
    | n when n > 0 ->
      mismatch (Printf.sprintf
        "Missing subproofs (%d subproofs for %d subgoals)."
        nb_subproofs nb_newgoals)
    | _ ->
      mismatch (Printf.sprintf
        "Too many subproofs (%d subproofs for %d subgoals)."
        nb_subproofs nb_newgoals)
