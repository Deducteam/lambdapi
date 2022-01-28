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

(** Function for printing a pair of terms as a rule. *)
let rule : (term * term) pp = fun ppf (l,r) -> out ppf "%a ↪ %a" term l term r

(** Type for pattern variable substitutions. *)
type subs = term IntMap.t

let subs : term IntMap.t pp =
  let var ppf i = if i >= 0 then out ppf "$%d" i else out ppf "$%d'" (-i-1) in
  D.map IntMap.iter var " ≔ " term "; "

(** Type for a symbol with a rule. *)
type sym_rule = sym * rule

let lhs : sym_rule -> term = fun (s, r) -> add_args (mk_Symb s) r.lhs
let rhs : sym_rule -> term = fun (_, r) -> LibTerm.term_of_rhs r

let sym_rule : sym_rule pp = fun ppf r -> rule ppf (lhs r, rhs r)

(** [is_ho r] says if [r] uses higher-order variables. *)
let is_ho : rule -> bool = fun r -> Array.exists (fun i -> i > 0) r.arities

(** [is_definable s] says if [s] is definable and non opaque but not AC. *)
let is_definable : sym -> bool = fun s ->
  (match s.sym_prop with Defin | Injec -> true | _ -> false)
  && not s.sym_opaq

(** [is_defined s] says if [s] is defined and not AC. *)
let is_defined : sym -> bool = fun s ->
  is_definable s && (!(s.sym_rules) <> [] || !(s.sym_def) <> None)

(** [rule_of_def s d] creates the rule [s --> d]. *)
let rule_of_def : sym -> term -> rule = fun s d ->
  let rhs = Bindlib.unbox (Bindlib.bind_mvar [||] (Bindlib.box d)) in
  {lhs=[]; rhs; arity=0; arities=[||]; vars=[||]; xvars_nb=0;
   rule_pos=s.sym_pos}

(** [iter_subterms_eq pos f p t] iterates f on all subterms of [t] headed by a
   defined function symbol. [p] is the position of [t] in reverse order. *)
let iter_subterms_from_pos : subterm_pos ->
  Pos.popt -> (sym -> subterm_pos -> term -> unit) -> term -> unit =
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
let iter_subterms_eq :
  Pos.popt -> (sym -> subterm_pos -> term -> unit) -> term -> unit =
  iter_subterms_from_pos []

(** [iter_subterms pos f t] iterates f on all strict subterms of [t] headed by
   a defined function symbol. *)
let iter_subterms :
  Pos.popt -> (sym -> subterm_pos -> term -> unit) -> term -> unit =
  fun pos f t ->
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

(** [apply_subs s t] applies the pattern substitution [s] to [t]. *)
let apply_subs : term IntMap.t -> term -> term = fun s ->
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
      mk_Abst (apply_subs a,
               Bindlib.unbox (Bindlib.bind_var x (lift (apply_subs b))))
    | Prod(a,b) ->
      let x,b = Bindlib.unbind b in
      mk_Prod (apply_subs a,
               Bindlib.unbox (Bindlib.bind_var x (lift (apply_subs b))))
    | LLet(a,t,b) ->
      let x,b = Bindlib.unbind b in
      mk_LLet (apply_subs a, apply_subs t,
               Bindlib.unbox (Bindlib.bind_var x (lift (apply_subs b))))
    | Meta(m,ts) -> mk_Meta (m, Array.map apply_subs ts)
    | TEnv(te,ts) -> mk_TEnv (te, Array.map apply_subs ts)
    | TRef _ -> assert false
    | Wild -> assert false
    | Plac _ -> assert false
  in apply_subs

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
      (*if Logger.log_enabled() then
        log_cp "unif %a ≡ %a with %a" term t term u subs s;*)
      match t, u with
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
  let var i = mk_Patt (Some i, Format.sprintf "%d" i, [||]) in
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

(** [check_cp_subterm_rule pos l r p l_p g d] checks that, if [l_p] and [g]
   are unifiable with mgu [s], then [s(r)] and [s(l[d]_p)] are
   joinable. Precondition: [l] and [r] must have distinct indexes in Patt
   subterms. *)
let check_cp_subterm_rule :
  Pos.popt -> term -> term -> subterm_pos -> term -> term -> term -> unit =
  fun pos l r p l_p g d ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterm_rule \
            @[<v>l ≔ %a@ r ≔ %a@ p ≔ %a@ l_p ≔ %a@ g ≔ %a@ d ≔ %a]"
      term l term r subterm_pos p term l_p term g term d;*)
  match unif pos l_p g with
  | Some s ->
    (*if Logger.log_enabled() then
      log_cp "@[<v>s ≔ %a@ replace l p d ≔ %a]" subs s term (replace l p d);*)
    let r1 = apply_subs s r and r2 = apply_subs s (replace l p d) in
    Console.out 2 "@[<v>Critical pair:@ \
                   t ≔ %a@ \
                   t ↪[] %a@   \
                     with %a@ \
                   t ↪%a %a@   \
                     with %a]"
        term (apply_subs s l) term r1 rule (l,r)
        subterm_pos p term r2 rule (g,d);
    if not (Eval.eq_modulo [] r1 r2) then
      wrn pos "@[<v>Unjoinable critical pair:@ \
               t ≔ %a@ \
               t ↪[] %a@   \
                 with %a@ \
               t ↪%a %a@   \
                 with %a]"
        term (apply_subs s l) term r1 rule (l,r)
        subterm_pos p term r2 rule (g,d)
  | None -> ()

(** [check_cp_subterms_rule pos sr1 sr2] checks the critical pairs between all
   the strict subterms of the [sr1] LHS and the [sr2] LHS. *)
let check_cp_subterms_rule : Pos.popt -> sym_rule -> sym_rule -> unit =
  fun pos lr gd ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterms@.%a@.%a" Print.rule lr Print.rule gd;*)
  let l = lhs lr and r = rhs lr and g = lhs gd and d = rhs gd in
  let l = shift l and r = shift r in
  let f _ p l_p = check_cp_subterm_rule pos l r p l_p g d in
  iter_subterms pos f l

(** [check_cp_subterms_eq_rule pos sr1 sr2] checks the critical pairs between
   all the subterms of the [sr1] LHS and the [sr2] LHS. *)
let check_cp_subterms_eq_rule : Pos.popt -> sym_rule -> sym_rule -> unit =
  fun pos lr gd ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterms@.%a@.%a" Print.rule lr Print.rule gd;*)
  let l = lhs lr and r = rhs lr and g = lhs gd and d = rhs gd in
  let l = shift l and r = shift r in
  let f _ p l_p = check_cp_subterm_rule pos l r p l_p g d in
  iter_subterms_eq pos f l

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

(** [check_cp_subterms_eq pos sr1] checks the critical pairs between
   all the subterms of the [sr1] LHS and all the possible rule LHS's. *)
let check_cp_subterms_eq : Pos.popt -> sym_rule -> unit =
  fun pos ((_,x) as lr) ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterms@.%a@.%a" Print.rule lr Print.rule gd;*)
  let l = shift (lhs lr) and r = shift (rhs lr) in
  let f s p l_p =
    match !(s.sym_def) with
    | Some d -> check_cp_subterm_rule pos l r p l_p (mk_Symb s) d
    (*FIXME? what if s is applied to some arguments? *)
    | None ->
      match p with
      | [] ->
        let h y = if y != x then let gd = (s,y) in
            check_cp_subterm_rule pos l r p l_p (lhs gd) (rhs gd)
        in
        iter_rules h s !(s.sym_rules);
      | _ ->
        let h y = let gd = (s, y) in
          check_cp_subterm_rule pos l r p l_p (lhs gd) (rhs gd) in
        iter_rules h s !(s.sym_rules)
  in
  iter_subterms_eq pos f l

(** [iter_head_tail f l] iterates [f] on all pairs (head, tail) of [l]. *)
let rec iter_head_tail : ('a -> 'a list -> unit) -> 'a list -> unit =
  fun f l ->
  match l with
  | [] -> ()
  | h::t -> f h t; iter_head_tail f t

(** [check_cp_rules pos rs] checks all the critical pairs of [rs] with
   itself. *)
let check_cp_rules : Pos.popt -> sym_rule list -> unit = fun pos rs ->
  let f r rs =
    if can_handle r then begin
      check_cp_subterms_rule pos r r;
      iter_sym_rules (check_cp_subterms_eq_rule pos r) rs
    end
  in
  iter_head_tail f rs

(** [check_cp_sign pos rs'] checks all the critical pairs between all the
   rules of the signature and [rs']. *)
let check_cp_sign : Pos.popt -> Sign.t -> rule list SymMap.t -> unit =
  fun pos sign sym_map ->
  let f s' rs' =
    match SymMap.find_opt s' !(sign.Sign.sign_cp_pos) with
    | None -> ()
    | Some cps ->
      let h (l,r,p,l_p) =
        let h' r' =
          let gd = (s',r') in
          check_cp_subterm_rule pos l r p l_p (lhs gd) (rhs gd)
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
  check_cp_rules pos srs;
  (* Verification of CP*(S,R). /!\ Here, we use the fact that decision trees
     include new rules for testing joinability, but new rules have not been
     added in the symbols yet. *)
  iter_sym_rules (check_cp_subterms_eq pos) srs;
  (* Verification of CP*(R,S). *)
  check_cp_sign pos sign sym_map;
  let f path str_map =
    if path != Unif_rule.path && str_map <> StrMap.empty then
      let sign =
        try Path.Map.find path !Sign.loaded with Not_found -> assert false
      in
      check_cp_sign pos sign sym_map
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
    let h r =
      let lr = (s,r) in let l = lhs lr and r = rhs lr in
      let h' s' p l_p = map := add_elt s' (l,r,p,l_p) !map
        (*if Logger.log_enabled() then
          log_cp "add_cp_pos %a ↪ %a, %a, %a"
            term l term r subterm_pos p term l_p*)
      in
      iter_subterms_eq pos h' l
    in
    iter_rules h s rs
  in
  SymMap.iter f rules_map; !map
