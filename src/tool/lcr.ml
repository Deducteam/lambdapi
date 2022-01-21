(** Compute critical pairs and check local confluence. *)

open Core open Term open Print
open Timed
open Common open Error
open Lplib open Base open Extra

let log_cp = Logger.make 'f' "lcr " "local confluence"
let log_cp = log_cp.pp

let pp_rule : (term * term) pp = fun ppf (l,r) ->
  out ppf "%a ↪ %a" pp_term l pp_term r

(** Symbol with rule. *)
type sym_rule = sym * rule

let lhs : sym_rule -> term = fun (s, r) -> add_args (mk_Symb s) r.lhs
let rhs : sym_rule -> term = fun (_, r) -> LibTerm.term_of_rhs r

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

(** Positions in terms: the i-th argument of a constructor has position
   i-1. *)
type subterm_pos = int list

let subterm_pos : subterm_pos pp = Debug.D.(list int)

(** [iter_subterms_eq pos f t] iterates f on all subterms of [t] headed by a
   defined function symbol. *)
(*
let iter_subterms_eq :
  Pos.popt -> (int list -> term -> unit) -> term -> unit =
  fun pos f t ->
  let rec iter p t =
    match get_args t with
    | Symb s, ts ->
      if is_defined s then f p t;
      List.iteri (fun i t -> iter (i::p) t) ts
    | Patt _, _
    | Vari _, _ -> ()
    | Abst(_a,_b), []
    | Prod(_a,_b), [] ->
      wrn pos "Ignore subterms of [%a]@ at position >= %a."
        pp_term t subterm_pos p
      (*iter (0::p) a; let _,b = Bindlib.unbind b in iter (1::p) b*)
    | Abst _, _ -> assert false
    | Prod _, _ -> assert false
    | Appl _, _ -> assert false
    | Type, _ -> assert false
    | Kind, _ -> assert false
    | Meta _, _ -> assert false
    | TEnv _, _ -> assert false
    | Wild, _ -> assert false
    | Plac _, _ -> assert false
    | TRef _, _ -> assert false
    | LLet _, _ -> assert false
  in iter [] t
*)

(** [iter_subterms_eq pos f p t] iterates f on all subterms of [t] headed by a
   defined function symbol. [p] is the position of [t] in reverse order. *)
let iter_subterms_from_pos :
  int list -> Pos.popt -> (sym -> int list -> term -> unit) -> term -> unit =
  fun p _pos f t ->
  let rec iter p t =
    (*if Logger.log_enabled() then
      log_cp "iter_subterms_eq %a %a" subterm_pos p pp_term t;*)
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
  Pos.popt -> (sym -> int list -> term -> unit) -> term -> unit =
  iter_subterms_from_pos []

(** [iter_subterms pos f t] iterates f on all strict subterms of [t] headed by
   a defined function symbol. *)
let iter_subterms :
  Pos.popt -> (sym -> int list -> term -> unit) -> term -> unit =
  fun pos f t ->
  (*if Logger.log_enabled() then log_cp "iter_subterms %a" pp_term t;*)
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
(*let replace : term -> int list -> term -> term = fun t p u ->
  let rec replace t p =
    match p with
    | [] -> u
    | i::p ->
      match get_args t with
      | Symb s, ts -> aux (mk_Symb s) i ts p
      | _ -> invalid_arg __LOC__
  and aux h i ts p =
    match ts with
    | [] -> assert false
    | t::ts ->
      if i <= 0 then add_args h (replace t p :: ts)
      else aux (mk_Appl (h, t)) (i-1) ts p
  in replace t p
*)

(** [replace t p u] replaces the subterm of [t] at position [p] by [u]. *)
let replace : term -> int list -> term -> term = fun t p u ->
  let rec replace t p =
    (*if Logger.log_enabled() then
      log_cp "replace [%a] %a" pp_term t subterm_pos p;*)
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
  in replace t (List.rev p)

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

(** [subs s t] applies the pattern substitution [s] to [t]. *)
let subs : term IntMap.t -> term -> term = fun s ->
  let rec subs t =
    match unfold t with
    | Patt(None, _, _) -> assert false
    | Patt(Some i,_,[||]) -> begin try IntMap.find i s with Not_found -> t end
    | Patt _ -> assert false
    | Vari _ | Symb _ | Type | Kind -> t
    | Appl(u,v) -> mk_Appl (subs u, subs v)
    | Abst(a,b) ->
      let x,b = Bindlib.unbind b in
      mk_Abst (subs a, Bindlib.unbox (Bindlib.bind_var x (lift (subs b))))
    | Prod(a,b) ->
      let x,b = Bindlib.unbind b in
      mk_Prod (subs a, Bindlib.unbox (Bindlib.bind_var x (lift (subs b))))
    | LLet(a,t,b) ->
      let x,b = Bindlib.unbind b in
      mk_LLet (subs a, subs t,
               Bindlib.unbox (Bindlib.bind_var x (lift (subs b))))
    | Meta(m,ts) -> mk_Meta (m, Array.map subs ts)
    | TEnv(te,ts) -> mk_TEnv (te, Array.map subs ts)
    | TRef _ -> assert false
    | Wild -> assert false
    | Plac _ -> assert false
  in subs

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
   s] with [s] the mgu otherwise. Precondition: [l] and [r] must have distinct
   indexes in Patt subterms. *)
(*let unif : Pos.popt -> term -> term -> term IntMap.t option =
  fun pos t u ->
  let is_patt i = function Patt(Some j,_,_) -> j=i | _ -> false in
  let exception NotUnifiable in
  let rec unif s = function
    | [] -> s
    | (t, u)::l ->
      match get_args t, get_args u with
      | (Symb f, ts), (Symb g, us) ->
        if f == g then
          let f l t u = (t,u)::l in
          let l' =
            try List.fold_left2 f l ts us
            with Invalid_argument _ -> raise NotUnifiable
          in
          unif s l'
        else raise NotUnifiable
      | (Patt(None,_,_), _), _
      | _, (Patt(None,_,_), _)
      | (Patt _, _::_), _
      | _, (Patt _, _::_)
        -> assert false
      | (Patt(Some i,_,_), _), _ ->
        begin match IntMap.find_opt i s with
          | Some t -> unif s ((t, u)::l)
          | None ->
            if is_patt i u then unif s l
            else if occurs i u then raise NotUnifiable
            else unif (IntMap.add i u s) l
        end
      | _, (Patt(Some i,_,_), _) ->
        begin
          match IntMap.find_opt i s with
          | Some u -> unif s ((t, u)::l)
          | None ->
            if occurs i t then raise NotUnifiable
            else unif (IntMap.add i t s) l
        end
      | _ ->
        wrn pos "Unification of non-algebraic terms not implemented yet.";
        raise NotUnifiable
  in try Some (unif IntMap.empty [t,u]) with NotUnifiable -> None
*)

let unif : Pos.popt -> term -> term -> term IntMap.t option =
  fun _pos t u ->
  let is_patt i = function Patt(Some j,_,_) -> j=i | _ -> false in
  let exception NotUnifiable in
  let rec unif s = function
    | [] -> s
    | (t, u)::l ->
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
      | Patt(Some i,_,ts), _ ->
        assert (Array.length ts = 0);
        begin match IntMap.find_opt i s with
          | Some t -> unif s ((t, u)::l)
          | None ->
            if is_patt i u then unif s l
            else if occurs i u then raise NotUnifiable
            else unif (IntMap.add i u s) l
        end
      | _, Patt(Some i,_,ts) ->
        assert (Array.length ts = 0);
        begin
          match IntMap.find_opt i s with
          | Some u -> unif s ((t, u)::l)
          | None ->
            if occurs i t then raise NotUnifiable
            else unif (IntMap.add i t s) l
        end
      | Type, Type
      | Kind, Kind -> unif s l
      | Meta _, _ | _, Meta _ -> assert false
      | TEnv _, _ | _, TEnv _ -> assert false
      | Wild, _ | _, Wild -> assert false
      | Plac _, _ | _, Plac _ -> assert false
      | TRef _, _ | _, TRef _ -> assert false
      | LLet _, _ | _, LLet _ -> assert false
      | _ -> raise NotUnifiable
  in try Some (unif IntMap.empty [t,u]) with NotUnifiable -> None

(* Unit tests. *)
let _ =
  let var i = mk_Patt (Some i, Format.sprintf "v%d" i, [||]) in
  let sym name =
    create_sym [] Public Defin Eager false (Pos.none name) mk_Type [] in
  let v0 = var 0 and v1 = var 1 and _v2 = var 2
  and f = sym "f" and g = sym "g" and _h = sym "h" in
  let app s ts = add_args (mk_Symb s) ts in
  let open IntMap in
  assert (unif None v0 v0 = Some empty);
  assert (unif None (app f []) (app f []) = Some empty);
  assert (unif None (app f [v0]) v1 = Some (add 1 (app f [v0]) empty));
  assert (unif None (app g [app f [v0]; v1]) (app g [v1; app f [v0]])
          = Some (add 1 (app f [v0]) empty));
  assert (unif None (app f []) (app g []) = None);
  assert (unif None v0 (app f [v0]) = None)

(** [check_cp_subterm_rule pos l r p l_p g d] checks that, if [l_p] and [g]
   are unifiable with mgu [s], then [s(r)] and [s(l[d]_p)] are
   joinable. Precondition: [l] and [r] must have distinct indexes in Patt
   subterms. *)
let check_cp_subterm_rule :
  Pos.popt -> term -> term -> int list -> term -> term -> term -> unit =
  fun pos l r p l_p g d ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterm_rule %a" pp_term l_p;*)
  match unif pos l_p g with
  | Some s ->
    let r1 = subs s r and r2 = subs s (replace l p d) in
    Console.out 2 "Critical pair:@.\
                   t ≔ %a@.\
                   t ↪[] %a@.  \
                     with %a@.\
                   t ↪%a %a@.  \
                     with %a"
        pp_term (subs s l) pp_term r1 pp_rule (l,r)
        subterm_pos p pp_term r2 pp_rule (g,d);
    if not (Eval.eq_modulo [] r1 r2) then
      wrn pos "Unjoinable critical pair:@.\
               t ≔ %a@.\
               t ↪[] %a@.  \
                 with %a@.\
               t ↪%a %a@.  \
                 with %a"
        pp_term (subs s l) pp_term r1 pp_rule (l,r)
        subterm_pos p pp_term r2 pp_rule (g,d)
  | None -> ()

(** [check_cp_subterms_rule pos sr1 sr2] checks the critical pairs between all
   the strict subterms of the [sr1] LHS and the [sr2] LHS. *)
let check_cp_subterms_rule : Pos.popt -> sym_rule -> sym_rule -> unit =
  fun pos lr gd ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterms@.%a@.%a" Print.pp_rule lr Print.pp_rule gd;*)
  let l = lhs lr and r = rhs lr and g = lhs gd and d = rhs gd in
  let l = shift l and r = shift r in
  let f _ p l_p = check_cp_subterm_rule pos l r p l_p g d in
  iter_subterms pos f l

(** [check_cp_subterms_eq_rule pos sr1 sr2] checks the critical pairs between
   all the subterms of the [sr1] LHS and the [sr2] LHS. *)
let check_cp_subterms_eq_rule : Pos.popt -> sym_rule -> sym_rule -> unit =
  fun pos lr gd ->
  (*if Logger.log_enabled() then
    log_cp "check_cp_subterms@.%a@.%a" Print.pp_rule lr Print.pp_rule gd;*)
  let l = lhs lr and r = rhs lr and g = lhs gd and d = rhs gd in
  let l = shift l and r = shift r in
  let f _ p l_p = check_cp_subterm_rule pos l r p l_p g d in
  iter_subterms_eq pos f l

(** [can_handle r] says if the sym_rule [r] can be handled. *)
let can_handle : sym_rule -> bool = fun (s,r) -> not (is_modulo s || is_ho r)

(** [iter_rules h rs] iterates function [f] on every rule of [rs]. *)
let iter_rules : (rule -> unit) -> rule list -> unit = fun h ->
  let rec iter = function
    | r::rs -> if not (is_ho r) then h r; iter rs
    | _ -> ()
  in iter

(** [iter_rules h rs] iterates function [f] on every rule of [rs]. *)
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
    log_cp "check_cp_subterms@.%a@.%a" Print.pp_rule lr Print.pp_rule gd;*)
  let l = shift (lhs lr) and r = shift (rhs lr) in
  let f s p l_p =
    match !(s.sym_def) with
    | Some d -> check_cp_subterm_rule pos l r p l_p (mk_Symb s) d
    | None ->
      match p with
      | [] ->
        let h y = if y != x then let gd = (s, y) in
            check_cp_subterm_rule pos l r p l_p (lhs gd) (rhs gd)
        in
        iter_rules h !(s.sym_rules);
      | _ ->
        let h y = let gd = (s, y) in
          check_cp_subterm_rule pos l r p l_p (lhs gd) (rhs gd) in
        iter_rules h !(s.sym_rules)
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

(** [check_cp_sign pos rs] checks all the critical pairs between all the rules
   of the signature and [rs]. *)
(*let check_cp_sign : Pos.popt -> Sign.t -> sym_rule list -> unit =
  fun pos sign rs ->
  (* TODO: to be optimized by recording in sym type some useful data to avoid
     traversing all LHS's again and again. *)
  (* We first build a map symbol s to new rules on s. *)
  let f _ s =
    if is_definable s then begin
      if Logger.log_enabled() then log_cp "check %a" pp_sym s;
      let h r = iter_sym_rules (check_cp_subterms_eq_rule pos (s,r)) rs in
      iter_rules_of_sym h s
    end
  in
  StrMap.iter f !(sign.Sign.sign_symbols)*)

(** [check_cp_sign pos rs] checks all the critical pairs between all the rules
   of the signature and [rs]. *)
let check_cp_sign : Pos.popt -> Sign.t -> sym_rule list -> unit =
  fun pos sign rs ->
  (* We build a map between a symbol and its new rules. *)
  let new_rules : rule list SymMap.t =
    let f map (s,r) =
      let h = function Some rs -> Some(r::rs) | None -> Some[r] in
      SymMap.update s h map in
    List.fold_left f SymMap.empty rs
  in
  (* [cp_positions s] maps every definable symbol s' such that there is a rule
     l-->r of [s] and a position p<>[] of l such that l_p is headed by s' to
     (p,l_p). *)
  let cp_positions : sym -> (term * term * int list * term) SymMap.t =
    fun s ->
    let map = Stdlib.ref SymMap.empty in
    let f r =
      let lr = (s,r) in let l = lhs lr and r = rhs lr in
      let h s' p l_p = Stdlib.(map := SymMap.add s' (l,r,p,l_p) !map) in
      iter_subterms pos h l
    in
    iter_rules_of_sym f s; Stdlib.(!map)
  in
  let f _ s =
    let h s' (l,r,p,l_p) =
      match SymMap.find_opt s' new_rules with
      | None -> ()
      | Some rs ->
        let h' r' =
          let gd = (s',r') in
          check_cp_subterm_rule pos l r p l_p (lhs gd) (rhs gd)
        in
        iter_rules h' rs
    in
    SymMap.iter h (cp_positions s)
  in
  StrMap.iter f !(sign.Sign.sign_symbols)

(** [check_cps rs] checks all the critical pairs generating by adding [rs]. *)
let check_cps : Pos.popt -> Sig_state.t -> sym_rule list -> unit =
  fun pos ss rs ->
  check_cp_rules pos rs;
  iter_sym_rules (check_cp_subterms_eq pos) rs;
  check_cp_sign pos ss.Sig_state.signature rs
(*FIXME: check dependencies too *)
