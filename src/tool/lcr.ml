(** Incremental verification of local confluence

by checking the joinability of critical pairs.

- CP(l-->r, p, g-->d) = { (s(r), s(l[d]_p) | s = mgu(l|_p,g) } is the critical
   pair between l|_p and g.

- CP*(l-->r, g-->d) = U { CP(l-->r, p, g-->d) | p in FPos(l) }

- CP*(R,S) = U { CP*(l-->r, g-->d) | l-->r in R, g-->d in S }

The set of critical pairs of a rewrite system R is CP(R) = CP*(R,R).

We have CP(R U S) = CP*(R,R) U CP*(R,S) U CP*(S,R) U CP*(S,S).

As a consequence, assuming that we already checked the local confluence of R
   and add a new set S of rules, we do not need to check CP*(R,R) again.

Warning: we currently do not take into account the rules having higher-order
   pattern variables and critical pairs on AC symbols.

Remark: When trying to unify a subterm of a rule LHS with the LHS of another
   rule, we need to rename the pattern variables of one of the LHS to avoid
   name clashes. To this end, we use the [shift] function below which replaces
   [Patt(i,n,_)] by [Patt(-i-1,n ^ "'",_)]. The printing function [subs] below
   takes this into account. *)

open Core open Term open Print
open Timed
open Common open Error open Debug
open Lplib open Base open Extra

let log_cp = Logger.make 'k' "lcr " "local confluence"
let log_cp = log_cp.pp

(** [rule_of_pair ppf x] prints on [ppf] the pair of term [x] as a rule. *)
let rule_of_pair : (term * term) pp =
  fun ppf (l,r) -> out ppf "%a ↪ %a" term l term r

(** [is_ho r] says if [r] uses higher-order variables. *)
let is_ho : rule -> bool = fun r -> Array.exists (fun i -> i > 0) r.arities

(** [is_definable s] says if [s] is definable and non opaque but not AC. *)
let is_definable : sym -> bool = fun s ->
  (match s.sym_prop with Defin | Injec -> true | _ -> false)
  && not s.sym_opaq

(** [rule_of_def s d] creates the rule [s --> d]. *)
let rule_of_def : sym -> term -> rule = fun s d ->
  let rhs = Bindlib.unbox (Bindlib.bind_mvar [||] (Bindlib.box d)) in
  {lhs=[]; rhs; arity=0; arities=[||]; vars=[||]; xvars_nb=0;
   rule_pos=s.sym_pos}

(** [replace t p u] replaces the subterm of [t] at position [p] by [u]. *)
let replace : term -> subterm_pos -> term -> term = fun t p u ->
  (*if Logger.log_enabled() then log_cp "replace by %a" term u;*)
  let rec replace t p =
    (*if Logger.log_enabled() then
      log_cp "at %a in %a" subterm_pos p term t;*)
    match p with
    | [] -> u
    | 0::p ->
      begin match unfold t with
        | Appl(a,b) -> mk_Appl (replace a p, b)
        | Abst(a,b) -> mk_Abst (replace a p, b)
        | Prod(a,b) -> mk_Prod (replace a p, b)
        | _ -> assert false
      end
    | 1::p ->
      begin match unfold t with
        | Appl(a,b) -> mk_Appl (a, replace b p)
        | _ -> assert false
      end
    | _ -> assert false
  in replace t (List.rev p) (* positions are in reverse order *)

(** [occurs i t] returns [true] iff [Patt(i,_,_)] is a subterm of [t]. *)
let occurs : int -> term -> bool = fun i ->
  let rec occ t =
    match unfold t with
    | Patt(None,_,_) -> assert false
    | Patt(Some j,_,_) -> i=j
    | Vari _ | Symb _ -> false
    | Appl(u,v) -> occ u || occ v
    | Abst(a,b) | Prod(a,b) -> occ a || let _,b = Bindlib.unbind b in occ b
    | Type -> assert false
    | Kind -> assert false
    | Meta _ -> assert false
    | TEnv _ -> assert false
    | Wild -> assert false
    | Plac _ -> assert false
    | TRef _ -> assert false
    | LLet _ -> assert false
  in occ

(** [shift t] replaces in [t] every pattern index i by -i-1. *)
let shift : term -> term =
  let rec shift : term -> tbox = fun t ->
    match unfold t with
    | Vari x -> _Vari x
    | Type -> _Type
    | Kind -> _Kind
    | Symb _ -> Bindlib.box t
    | Prod(a,b) -> _Prod (shift a) (shift_binder b)
    | Abst(a,b) -> _Abst (shift a) (shift_binder b)
    | Appl(a,b) -> _Appl (shift a) (shift b)
    | Meta(m,ts) -> _Meta m (Array.map shift ts)
    | Patt(None,_,_) -> assert false
    | Patt(Some i,n,ts) -> _Patt (Some(-i-1)) (n ^ "'") (Array.map shift ts)
    | TEnv(te,ts) -> _TEnv (shift_tenv te) (Array.map shift ts)
    | Wild -> _Wild
    | Plac b -> _Plac b
    | TRef r -> _TRef r
    | LLet(a,t,b) -> _LLet (shift a) (shift t) (shift_binder b)
  and shift_binder b =
    let x, t = Bindlib.unbind b in Bindlib.bind_var x (shift t)
  and shift_tenv : term_env -> tebox = function
    | TE_Vari x -> _TE_Vari x
    | TE_None -> _TE_None
    | TE_Some _ -> assert false
  in fun t -> Bindlib.unbox (shift t)

(** Type for pattern variable substitutions. *)
type subs = term IntMap.t

let subs : term IntMap.t pp =
  let var ppf i = if i >= 0 then out ppf "$%d" i else out ppf "$%d'" (-i-1) in
  D.map IntMap.iter var " ≔ " term "; "

(** [apply_subs s t] applies the pattern substitution [s] to [t]. *)
let apply_subs : subs -> term -> term = fun s t ->
  (*if Logger.log_enabled() then log_cp "apply_subs by %a" subs s;*)
  let rec apply_subs t =
    (*if Logger.log_enabled() then log_cp "%a" term t;*)
    match unfold t with
    | Patt(None, _, _) -> assert false
    | Patt(Some i,_,[||]) ->
      begin try IntMap.find i s with Not_found -> t end
    | Patt(i,n,ts) -> mk_Patt (i, n, Array.map apply_subs ts)
    | Vari _ | Symb _ | Type | Kind -> t
    | Appl(u,v) -> mk_Appl (apply_subs u, apply_subs v)
    | Abst(a,b) ->
      let x,b = Bindlib.unbind b in
      mk_Abst (apply_subs a, bind x lift (apply_subs b))
    | Prod(a,b) ->
      let x,b = Bindlib.unbind b in
      mk_Prod (apply_subs a, bind x lift (apply_subs b))
    | LLet(a,t,b) ->
      let x,b = Bindlib.unbind b in
      mk_LLet (apply_subs a, apply_subs t, bind x lift (apply_subs b))
    | Meta(m,ts) -> mk_Meta (m, Array.map apply_subs ts)
    | TEnv(te,ts) -> mk_TEnv (te, Array.map apply_subs ts)
    | TRef _ -> assert false
    | Wild -> assert false
    | Plac _ -> assert false
  in if IntMap.is_empty s then t else apply_subs t

(** Type of subterm iterators. *)
type iter = Pos.popt -> (sym -> subterm_pos -> term -> unit) -> term -> unit

(** [iter_subterms_eq pos f p t] iterates f on all subterms of [t] headed by a
   defined function symbol. [p] is the position of [t] in reverse order. *)
let iter_subterms_from_pos : subterm_pos -> iter =
  fun p _pos f t ->
  let rec iter p t =
    (*if Logger.log_enabled() then
      log_cp "iter_subterms_eq %a %a" subterm_pos p term t;*)
    let h, _ = get_args t in
    match unfold h with
    | Symb s -> if is_definable s then iter_app s p t else iter_args p t
    | Patt _
    | Vari _ -> iter_args p t
    | Abst(a,b)
    | Prod(a,b) -> iter (0::p) a; let _,b = Bindlib.unbind b in iter (1::p) b
    | Appl _ -> assert false
    | Type -> assert false
    | Kind -> assert false
    | Meta _ -> assert false
    | TEnv _ -> assert false
    | Wild -> assert false
    | Plac _ -> assert false
    | TRef _ -> assert false
    | LLet _ -> assert false
  and iter_app s p t =
    f s p t;
    match unfold t with
    | Appl(a,b) -> iter (1::p) b; iter_app s (0::p) a
    | _ -> ()
  and iter_args p t =
    match unfold t with
    | Appl(a,b) -> iter (1::p) b; iter_args (0::p) a
    | _ -> ()
  in iter p t

(** [iter_subterms_eq pos f t] iterates f on all subterms of [t] headed by a
   defined function symbol. *)
let iter_subterms_eq : iter = iter_subterms_from_pos []

(** [iter_subterms pos f t] iterates f on all strict subterms of [t] headed by
   a defined function symbol. *)
let iter_subterms : iter = fun pos f t ->
  (*if Logger.log_enabled() then log_cp "iter_subterms %a" term t;*)
  match unfold t with
  | Symb _
  | Patt _
  | Vari _ -> ()
  | Abst(a,b)
  | Prod(a,b) ->
    iter_subterms_from_pos [0] pos f a;
    let _,b = Bindlib.unbind b in iter_subterms_from_pos [1] pos f b;
  | Appl(a,b) ->
    iter_subterms_from_pos [0] pos f a; iter_subterms_from_pos [1] pos f b;
  | Type -> assert false
  | Kind -> assert false
  | Meta _ -> assert false
  | TEnv _ -> assert false
  | Wild -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | LLet _ -> assert false

(** [unif pos t u] returns [None] if [t] and [u] are not unifiable, and [Some
   s] with [s] an idempotent mgu otherwise. Precondition: [l] and [r] must
   have distinct indexes in Patt subterms. *)
let unif : Pos.popt -> term -> term -> term IntMap.t option =
  fun _pos t u ->
  let is_patt i = function Patt(Some j,_,_) -> j=i | _ -> false in
  let exception NotUnifiable in
  let rec unif s = function
    | [] -> s
    | (t, u)::l ->
      if Logger.log_enabled() then
        log_cp "unif %a ≡ %a with %a" term t term u subs s;
      match unfold t, unfold u with
      | Symb f, Symb g -> if f == g then unif s l else raise NotUnifiable
      | Appl(a,b), Appl(c,d) -> unif s ((a,c)::(b,d)::l)
      | Abst(a,b), Abst(c,d)
      | Prod(a,b), Prod(c,d) ->
        let x,b = Bindlib.unbind b in
        let d = Bindlib.subst d (mk_Vari x) in
        unif s ((a,c)::(b,d)::l)
      | Vari x, Vari y ->
        if Bindlib.eq_vars x y then unif s l else raise NotUnifiable
      | Patt(None,_,_), _
      | _, Patt(None,_,_) -> assert false
      | Patt(Some i,_,ts), u
      | u, Patt(Some i,_,ts) -> unif_patt s i ts u l
      | Type, Type
      | Kind, Kind -> unif s l
      | Meta _, _ | _, Meta _ -> assert false
      | TEnv _, _ | _, TEnv _ -> assert false
      | Wild, _ | _, Wild -> assert false
      | Plac _, _ | _, Plac _ -> assert false
      | TRef _, _ | _, TRef _ -> assert false
      | LLet _, _ | _, LLet _ -> assert false
      | _ -> raise NotUnifiable
  and unif_patt s i ts u l =
    assert (Array.length ts = 0);
    if is_patt i u then unif s l
    else if occurs i u then raise NotUnifiable
    else let s0 = IntMap.singleton i u in
      let s' = IntMap.add i u (IntMap.map (apply_subs s0) s) in
      let f (a,b) = apply_subs s' a, apply_subs s' b in
      unif s' (List.map f l)
  in try Some (unif IntMap.empty [t,u]) with NotUnifiable -> None

(* Unit tests. *)
let _ =
  let var i = mk_Patt (Some i, string_of_int i, [||]) in
  let v0 = var 0
  and v1 = var 1 in
  let sym name =
    create_sym [] Public Defin Eager false (Pos.none name) mk_Type [] in
  let a_ = sym "a"
  and b_ = sym "b"
  and s_ = sym "s"
  and f_ = sym "f" in
  let app s ts = add_args (mk_Symb s) ts in
  let a = app a_ []
  and b = app b_ []
  and s t = app s_ [t]
  and f t u = app f_ [t; u] in
  let open IntMap in
  let unif = unif None in
  assert (unif v0 v0 = Some empty);
  assert (unif a a = Some empty);
  assert (unif (s v0) v1 = Some (add 1 (s v0) empty));
  assert (unif (f (s v0) v1) (f v1 (s v0)) = Some (add 1 (s v0) empty));
  assert (unif a b = None);
  assert (unif v0 (s v0) = None)

(** [can_handle r] says if the sym_rule [r] can be handled. *)
let can_handle : sym_rule -> bool = fun (s,r) -> not (is_modulo s || is_ho r)

(** [iter_rules h rs] iterates function [f] on every rule of [rs]. *)
let iter_rules : (rule -> unit) -> sym -> rule list -> unit = fun h ->
  let rec iter = function
    | r::rs -> if not (is_ho r) then h r; iter rs
    | _ -> ()
  in
  fun s rs -> if not (is_modulo s) then iter rs

(** [iter_sym_rules h rs] iterates function [f] on every rule of [rs]. *)
let iter_sym_rules : (sym_rule -> unit) -> sym_rule list -> unit = fun h ->
  let rec iter = function
    | [] -> ()
    | r::rs -> if can_handle r then h r; iter rs
  in iter

(** [iter_rules_of_sym h s] iterates [f] on every rule of [s]. *)
let iter_rules_of_sym : (rule -> unit) -> sym -> unit = fun h s ->
  if not (is_modulo s) then
    match !(s.sym_def) with
    | None -> List.iter (fun r -> if not (is_ho r) then h r) !(s.sym_rules)
    | Some d -> h (rule_of_def s d)

(** Type of rule identifiers. Hack: we use the rule position to distinguish
   between user-defined and generated rules (in completion), by giving a
   unique negative start_line to every generated rule. *)
type rule_id = Pos.pos

(** [id_sym_rule r] returns the rule id of [r]. *)
let id_sym_rule : sym_rule -> rule_id = fun (_,r) ->
  match r.rule_pos with Some p -> p | _ -> assert false

(** [new_rule_id()] generates a new unique rule id. *)
let new_rule_id : unit -> rule_id =
  let open Stdlib in let n = ref 0 in fun () -> decr n;
  {fname=None; start_line=(!n); start_col=0; end_line=0; end_col=0}

(** [is_generated i] says if [i] is a generated rule id. *)
let is_generated : rule_id -> bool = fun p -> p.start_line < 0

(** [int_of_rule_id i] returns a unique integer from [i]. /!\ [i] must be a
   generated rule. *)
let int_of_rule_id : rule_id -> int = fun i ->
  assert (is_generated i); i.start_line

(** Type of functions on critical pairs. *)
type cp_fun =
  Pos.popt (* position for error messages *)
  -> rule_id -> term -> term (* rule l --> r *)
  -> subterm_pos -> term (* subterm position p and subterm l_p *)
  -> rule_id -> term -> term (* rule g --> d *)
  -> subs (* mgu(l_p,g) *)
  -> unit

(** Type of functions on critical pair candidates. *)
type cp_cand_fun =
  Pos.popt
  -> rule_id -> term -> term
  -> subterm_pos -> term
  -> rule_id -> term -> term
  -> unit

(** [cp_cand_fun] turns a cp_fun into a cp_cand_fun. *)
let cp_cand_fun : cp_fun -> cp_cand_fun = fun h pos i l r p l_p j g d ->
  Option.iter (h pos i l r p l_p j g d) (unif pos l_p g)

(** [iter_cps_with_rule iter_subterms h pos sr1 sr2] applies [h] on all the
   critical pairs between all the subterms of the [sr1] LHS and the [sr2] LHS
   using the iterator [iter_subterms]. *)
let iter_cps_with_rule :
  iter -> cp_fun -> Pos.popt -> sym_rule -> sym_rule -> unit =
  fun iter_subterms h pos lr gd ->
  (*if Logger.log_enabled() then
    log_cp "iter_cps_with_rule@.%a@.%a" Print.rule lr Print.rule gd;*)
  let l = lhs lr and r = rhs lr and g = lhs gd and d = rhs gd in
  let l = shift l and r = shift r in
  let i = id_sym_rule lr and j = id_sym_rule gd in
  let f _ p l_p = cp_cand_fun h pos i l r p l_p j g d in
  iter_subterms pos f l

(** [iter_cps_of_rules h pos rs] applies [h] on all the critical pairs of [rs]
   with itself. *)
let iter_cps_of_rules : cp_fun -> Pos.popt -> sym_rule list -> unit =
  fun h pos rs ->
  let f r rs =
    if can_handle r then begin
      iter_cps_with_rule iter_subterms h pos r r;
      iter_sym_rules (iter_cps_with_rule iter_subterms_eq h pos r) rs
    end
  in
  List.iter_head_tail f rs

(** [typability_constraints pos t] returns [None] if [t] is not typable, and
   [Some s] where [s] is a substitution implied by the typability of [t]. *)
let typability_constraints : Pos.popt -> term -> subs option = fun pos t ->
  (* Replace Patt's by Meta's. *)
  let open Stdlib in
  let p = new_problem()
  and p2m : meta IntMap.t ref = ref IntMap.empty
  and m2p : (int * string) MetaMap.t ref = ref MetaMap.empty in
  if Logger.log_enabled() then log_cp "typability_constraints %a" term t;
  let rec patt_to_meta : term -> term = fun t ->
    match unfold t with
    | Patt(Some i,n,[||]) ->
      let m =
        match IntMap.find_opt i !p2m with
        | Some m -> m
        | None ->
          let m_typ = LibMeta.fresh p mk_Type 0 in
          let typ = mk_Meta(m_typ,[||]) in
          let m = LibMeta.fresh p typ 0 in
          p2m := IntMap.add i m !p2m; m2p := MetaMap.add m (i,n) !m2p; m
      in mk_Meta(m,[||])
    | Appl(a,b) -> mk_Appl_not_canonical(patt_to_meta a, patt_to_meta b)
    | Symb _ | Vari _ -> t
    | Abst(a,b) ->
      let x,b = Bindlib.unbind b in
      mk_Abst(patt_to_meta a, bind x lift_not_canonical (patt_to_meta b))
    | _ -> assert false
  in
  let t = patt_to_meta t in
  match Infer.infer_noexn p [] t with
  | None -> if Logger.log_enabled() then log_cp "not typable"; None
  | _ ->
  (* Replace unsolved metas by symbols. *)
  let s2p : int SymMap.t ref = ref SymMap.empty in
  let meta_to_sym : meta -> unit = fun m ->
    try
      let i,n = MetaMap.find m !m2p in
      let s = create_sym (Sign.current_path())
          Public Defin Eager false (Pos.none n) mk_Kind [] in
      let t = Bindlib.unbox (Bindlib.bind_mvar [||] (_Symb s)) in
      Timed.(m.meta_value := Some t);
      s2p := SymMap.add s i !s2p
    with Not_found -> ()
  in
  MetaSet.iter meta_to_sym Timed.(!p).metas;
  if Logger.log_enabled() then log_cp "meta_to_sym %a" problem p;
  (* Try to solve constraints. *)
  match Unif.solve_noexn ~type_check:false p with
  | false ->
    if Logger.log_enabled() then log_cp "unsolvable constraints"; None
  | true ->
  if Logger.log_enabled() then log_cp "after solve %a" problem p;
  (* Function replacing generated symbols by their corresponding Patt. *)
  let rec sym_to_patt : term -> term = fun t ->
    match unfold t with
    | Symb s ->
      begin match SymMap.find_opt s !s2p with
        | Some i -> mk_Patt(Some i, s.sym_name, [||])
        | None -> t
      end
    | Appl(a,b) -> mk_Appl_not_canonical(sym_to_patt a, sym_to_patt b)
    | _ -> t
  in
  (* Function converting a pair of terms into a rule, if possible. *)
  let rule_of_terms : term -> term -> sym_rule option = fun l r ->
    match get_args_len l with
    | Symb s, lhs, arity ->
      let vars = [||] and rule_pos = Some (new_rule_id()) in
      let rhs = Bindlib.unbox (Bindlib.bind_mvar vars (Bindlib.box r)) in
      let r = {lhs; rhs; arity; arities=[||]; vars; xvars_nb=0; rule_pos} in
      Some (s,r)
    | _ -> None
  in
  (* Turn constraints into rules. *)
  let add_constr : sym_rule IntMap.t -> constr -> sym_rule IntMap.t =
    fun rule_map (_,l,r) ->
    let l,r = if Term.cmp l r > 0 then l,r else r,l in
    match rule_of_terms l r with
    | Some x ->
      let i = id_sym_rule x in IntMap.add (int_of_rule_id i) x rule_map
    | _ -> rule_map
  in
  let rule_map =
    List.fold_left add_constr IntMap.empty Timed.(!p).unsolved in
  (* [completion_step rule_map] computes a possibly new rule map by
     simplifying [rule_map]. In case no rule has been removed or added, the
     resulting map is physically equal to [rule_map]. *)
  let completion_step : sym_rule IntMap.t -> sym_rule IntMap.t =
    fun rule_map ->
    if Logger.log_enabled() then
      log_cp "completion_step %a" (D.intmap sym_rule) rule_map;
    let new_rule_map = ref rule_map and modified = ref false in
    let remove_rule i =
      new_rule_map := IntMap.remove (int_of_rule_id i) !new_rule_map;
      modified := true
    in
    let add_rule l r =
      match rule_of_terms l r with
      | Some x ->
        let i = id_sym_rule x in
        new_rule_map := IntMap.add (int_of_rule_id i) x !new_rule_map;
        modified := true
      | None -> ()
    in
    let cp_fun _pos i l r p _l_p _j _g d s =
      assert (s = IntMap.empty);
      remove_rule i;
      let l' = replace l p d in
      match cmp l' r with
      | 0 -> ()
      | n when n > 0 -> add_rule l' r
      | _ -> add_rule r l'
    in
    let rs = IntMap.fold (fun _ r rs -> r::rs) rule_map [] in
    iter_cps_of_rules cp_fun pos rs;
    if !modified then !new_rule_map else rule_map
  in
  (* Completion. *)
  let rec complete : sym_rule IntMap.t -> sym_rule IntMap.t =
    fun rule_map ->
    let new_rule_map = completion_step rule_map in
    if new_rule_map == rule_map then rule_map else complete new_rule_map
  in
  let rule_map = complete rule_map in
  (* Turn completed rules into a substitution. *)
  let f _ ((s,_) as x) subs =
    match SymMap.find_opt s !s2p with
    | Some i -> IntMap.add i (sym_to_patt (rhs x)) subs
    | None -> subs
  in
  let s = IntMap.fold f rule_map IntMap.empty in
  if Logger.log_enabled() then log_cp "typing subs %a" subs s;
  Some s

(** [check_cp pos _ l r p l_p _ g d s] checks that, if [l_p] and [g] are
   unifiable with mgu [s], then [s(r)] and [s(l[d]_p)] are
   joinable. Precondition: [l] and [r] must have distinct indexes in Patt
   subterms. *)
let check_cp : cp_fun = fun pos _ l r p l_p _ g d s ->
  if Logger.log_enabled() then
    log_cp (Color.blu "check_cp \
      @[<v>l ≔ %a@ r ≔ %a@ p ≔ %a@ l_p ≔ %a@ g ≔ %a@ d ≔ %a@ s ≔ %a@]")
      term l term r subterm_pos p term l_p term g term d subs s;
  let t = apply_subs s l in
  match typability_constraints pos t with
  | None -> ()
  | Some s' ->
  let t = apply_subs s' t in
  let r1 = apply_subs s' (apply_subs s r)
  and r2 = apply_subs s' (apply_subs s (replace l p d)) in
  Console.out 2 "@[<v>Critical pair:@ \
                 t ≔ %a@ \
                 t ↪[] %a@   \
                   with %a@ \
                 t ↪%a %a@   \
                   with %a@]"
    term t term r1 rule_of_pair (l,r)
    subterm_pos p term r2 rule_of_pair (g,d);
  if not (Eval.eq_modulo [] r1 r2) then
    wrn pos "@[<v>Unjoinable critical pair:@ \
             t ≔ %a@ \
             t ↪[] %a ↪* %a@   \
               with %a@ \
             t ↪%a %a ↪* %a@   \
               with %a@]"
      term t term r1 term (Eval.snf [] r1) rule_of_pair (l,r)
      subterm_pos p term r2 term (Eval.snf [] r2) rule_of_pair (g,d)

(** [check_cps_subterms_eq pos sr1] checks the critical pairs between
   all the subterms of the [sr1] LHS and all the possible rule LHS's. *)
let check_cps_subterms_eq : Pos.popt -> sym_rule -> unit =
  fun pos ((_,x) as lr) ->
  (*if Logger.log_enabled() then
    log_cp "check_cps_subterms_eq@.%a@.%a" Print.rule lr Print.rule gd;*)
  let l = shift (lhs lr) and r = shift (rhs lr) in
  let i = id_sym_rule lr in
  let f s p l_p =
    match !(s.sym_def) with
    | Some d ->
      let j = match s.sym_pos with Some p -> p | None -> assert false in
      cp_cand_fun check_cp pos i l r p l_p j (mk_Symb s) d
    (*FIXME? what if s is applied to some arguments? *)
    | None ->
      let h y =
        let gd = (s, y) in let j = id_sym_rule gd in
        cp_cand_fun check_cp pos i l r p l_p j (lhs gd) (rhs gd)
      in
      match p with
      | [] -> let h y = if y != x then h y in iter_rules h s !(s.sym_rules);
      | _ -> iter_rules h s !(s.sym_rules)
  in
  iter_subterms_eq pos f l

(** [check_cps_sign_with pos rs'] checks all the critical pairs between all
   the rules of the signature and [rs']. *)
let check_cps_sign_with : Pos.popt -> Sign.t -> rule list SymMap.t -> unit =
  fun pos sign sym_map ->
  let f s' rs' =
    match SymMap.find_opt s' !(sign.Sign.sign_cp_pos) with
    | None -> ()
    | Some cps ->
      let h (i,l,r,p,l_p) =
        let h' r' =
          let i = match i with Some p -> p | None -> assert false in
          let gd = (s',r') in let j = id_sym_rule gd in
          cp_cand_fun check_cp pos i l r p l_p j (lhs gd) (rhs gd)
        in List.iter h' rs'
      in
      List.iter h cps
  in
  SymMap.iter f sym_map

(** [check_cps rs] checks all the critical pairs generated by adding [rs]. *)
let check_cps :
  Pos.popt -> Sign.t -> sym_rule list -> rule list SymMap.t -> unit =
  fun pos sign srs sym_map ->
  (* Verification of CP*(S,S). *)
  iter_cps_of_rules check_cp pos srs;
  (* Verification of CP*(S,R). /!\ Here, we use the fact that decision trees
     include new rules for testing joinability, but new rules have not been
     added in the symbols yet. *)
  iter_sym_rules (check_cps_subterms_eq pos) srs;
  (* Verification of CP*(R,S). *)
  check_cps_sign_with pos sign sym_map;
  let f path str_map =
    if path != Unif_rule.path && str_map <> StrMap.empty then
      let sign =
        try Path.Map.find path !Sign.loaded with Not_found -> assert false
      in
      check_cps_sign_with pos sign sym_map
  in
  Path.Map.iter f !(sign.sign_deps)

(** [update_cp_pos pos map rs] extends [map] by mapping every definable symbol
   s' such that there is a rule l-->r of [rs] and a position p of l such that
   l_p is headed by s' to (l,r,p,l_p). *)
let update_cp_pos : Pos.popt -> cp_pos list SymMap.t -> rule list SymMap.t ->
  cp_pos list SymMap.t =
  let add_elt : sym -> 'a -> 'a list SymMap.t -> 'a list SymMap.t =
    fun s x map ->
    let h = function None -> Some[x] | Some xs -> Some(x::xs) in
    SymMap.update s h map
  in
  fun pos cp_pos_map rules_map ->
  let open Stdlib in
  let map = ref cp_pos_map in
  let f s rs =
    let h ({rule_pos=i;_} as r) =
      let lr = (s,r) in let l = lhs lr and r = rhs lr in
      let h' s' p l_p = map := add_elt s' (i,l,r,p,l_p) !map
        (*if Logger.log_enabled() then
          log_cp "add_cp_pos %a ↪ %a, %a, %a"
            term l term r subterm_pos p term l_p*)
      in
      iter_subterms_eq pos h' l
    in
    iter_rules h s rs
  in
  SymMap.iter f rules_map; !map
