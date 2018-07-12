(** Type-checking and inference. *)

open Extra
open Timed
open Console
open Terms
open Print

(** Logging function for unification. *)
let log_solv = new_logger 's' "solv" "debugging information for unification"
let log_solv = log_solv.logger

(** Representation of unification problems. *)
type unif = term * term

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** [instantiate m ts v] check whether [m] can be instantiated to
    solve the unification problem [m[ts] = v]. Actually make the
    instantiation if it is possible. *)
let instantiate : meta -> term array -> term -> bool = fun m ar v ->
  (!can_instantiate || internal m) && distinct_vars ar && not (occurs m v) &&
  let bv = Bindlib.bind_mvar (to_tvars ar) (lift v) in
  Bindlib.is_closed bv && (set_meta m (Bindlib.unbox bv); true)

(** [eq_vari t u] checks that [t] and [u] are both variables, and the they are
    pariwise equal. *)
let eq_vari : term -> term -> bool = fun t u ->
  match (unfold t, unfold u) with
  | (Vari(x), Vari(y)) -> Bindlib.eq_vars x y
  | (_      , _      ) -> false

(*
let inst = instantiate

let unify : (term * term) list -> (term * term) list =
  let eq_vars = Array.for_all2 eq_vari in
  let rec unify acc l =
    match l with
    | []         -> acc
    | (t1,t2)::l ->
    match (unfold t1, unfold t2) with
    (* Leaves. *)
    | (Type       , Type       )
    | (Kind       , Kind       )                          -> unify acc l
    | (Vari(x)    , Vari(y)    ) when Bindlib.eq_vars x y -> unify acc l
    | (Symb(s)    , Symb(r)    ) when s == r              -> unify acc l
    (* Binders (abstractions and products). *)
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) -> unify acc ((a1,a2)::(unbind2 b1 b2)::l)
    (* Metavariable (reflexivity). *)
    | (Meta(m1,a1), Meta(m2,a2)) when m1 == m2 && eq_vars a1 a2 -> unify acc l
    (* Metavariable (instantiation). *)
    | (Meta(m,ar) , t          )
    | (t          , Meta(m,ar) ) ->
        if inst m ar t then unify acc l else
        let t = Eval.whnf t in
        if inst m ar t then unify acc l else
        let t = Eval.snf t in
        if inst m ar t then unify acc l else
        unify ((Meta(m,ar), t)::acc) l
    (* May need normalization (one side not in WHNF). *)
    | (Symb(s)    , _          ) when not (Sign.is_const s) ->
        unify_whnf acc l t1 t2
    | (_          , Symb(s)    ) when not (Sign.is_const s) ->
        unify_whnf acc l t1 t2
    | (Appl(_,_)  , _          )
    | (_          , Appl(_,_)  ) ->
        unify_whnf acc l t1 t2
    (* Definitely not convertible. *)
    | (_          , _          ) ->
        fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
  and unify_whnf acc l t1 t2 =
    let (h1, ts1) = Eval.whnf_stk t1 [] in
    let (h2, ts2) = Eval.whnf_stk t2 [] in
    if ts1 = [] && ts2 = [] then unify acc ((h1,h2)::l) else
    match (h1, h2) with
    (* Metavariable with no arguments. *)
    | (Meta(_,_)  , _          ) when ts1 = [] ->
        unify acc ((h1, Eval.to_term h2 ts2)::l)
    | (_          , Meta(_,_)  ) when ts2 = [] ->
        unify acc ((h2, Eval.to_term h1 ts1)::l)
    (* Non-necessarily injective head. *)
    | (Vari(x)    , Vari(y)    ) when Bindlib.eq_vars x y ->
        begin
          try
            let fn l t1 t2 = (!t1,!t2)::l in
            unify acc (List.fold_left2 fn l ts1 ts2)
          with Invalid_argument(_) ->
            let t1 = Eval.to_term h1 ts1 in
            let t2 = Eval.to_term h2 ts2 in
            fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
        end
    | (Symb(s1)   , Symb(s2)   ) when s1 == s2 && Sign.is_const s1 ->
        begin
          try
            let fn l t1 t2 = (!t1,!t2)::l in
            unify acc (List.fold_left2 fn l ts1 ts2)
          with Invalid_argument(_) ->
            let t1 = Eval.to_term h1 ts1 in
            let t2 = Eval.to_term h2 ts2 in
            fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
        end
    | (Symb(s)    , _          ) when not (Sign.is_const s) ->
        if Eval.eq_modulo t1 t2 then unify acc l
        else unify ((Eval.to_term h1 ts1, Eval.to_term h2 ts2)::acc) l
    | (_          , Symb(s)    ) when not (Sign.is_const s) ->
        if Eval.eq_modulo t1 t2 then unify acc l
        else unify ((Eval.to_term h1 ts1, Eval.to_term h2 ts2)::acc) l
    (* Definitely not convertible. *)
    | (_          , _          ) ->
        fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
  in
  unify []
*)

(** Representation of a set of problems. *)
type problems =
  { unif_problems : (term * term) list
  (** List of unification problems. *)
  ; whnf_problems : (term * term) list
  (** List of unification problems that must be put in WHNF first. *)
  ; unsolved      : (term * term) list
  (** List of unsolved unification problems. *)
  ; recompute     : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Empty problem. *)
let no_problems : problems =
  { unif_problems = []
  ; whnf_problems = []
  ; unsolved      = []
  ; recompute     = false }

let is_done : problems -> bool = fun p ->
  p.unif_problems = [] && p.whnf_problems = []

(** Representation of solving strategies. *)
type strategy = strategy_aux list
 and strategy_aux =
  | S_Unif             (** Deal with unification problems.      *)
  | S_Whnf             (** Deal with WHNF unification problems. *)
  | S_Done             (** Check if there is something to do.   *)
  | S_Loop of strategy (** Repeat a strategy indefinitely.      *)

(** [pp_strategy oc s] prints a representation of the strategy [s] to [oc]. *)
let pp_strategy : strategy pp =
  let rec pp_aux oc s =
    match s with
    | S_Unif    -> Format.fprintf oc "U"
    | S_Whnf    -> Format.fprintf oc "W"
    | S_Done    -> Format.fprintf oc "E"
    | S_Loop(l) -> Format.fprintf oc "[%a]" (List.pp pp_aux "") l
  in
  List.pp pp_aux ""

(** Default strategy. *)
let default_strategy : strategy =
  [S_Loop [S_Unif; S_Whnf; S_Done]]

(** [make_type ()] generates a fresh metavariable of arity [0], and which type
    is [Type]. *)
let make_type =
  let empty = [||] in
  fun () -> Meta(fresh_meta Type 0, empty)

(** [make_meta ctx a] creates a metavariable of type [a],  with an environment
    containing the variables of context [ctx]. *)
let make_meta : Ctxt.t -> term -> term = fun ctx a ->
  let m = fresh_meta (Ctxt.to_prod ctx a) (List.length ctx) in
  let vs = List.rev_map (fun (v,_) -> Vari v) ctx in
  Meta(m, Array.of_list vs)

(** [make_binder c n d] creates a binder obtained by binding v in the
    term [m[x1,..,xn,v]] of type a sort where [x1,..,xn] are the
    variables of [c] and [v] is a new variable of name [n]. *)
let make_binder : Ctxt.t -> string -> term -> tbinder = fun c n d ->
  let v = Bindlib.new_var mkfree n in
  let u = make_meta ((v,d)::c) (make_type()) in
  Bindlib.unbox (Bindlib.bind_var v (lift u))

(** [make_prod c] creates a term [x:m1[x1,..,xn]->m2[x1,..,xn,x]] of
    type a sort where [x1,..,xn] are the variables of [c] and [x] is a
    new variable of name [no]. *)
let make_prod c =
  let d = make_meta c (make_type()) in d, make_binder c "x" d

(** [solve s p] tries to solve the problem [p] following the strategy
    list [s]. When it stops, it returns the list of unsolved
    unification problems. *)
let rec solve : strategy -> problems -> unif list = fun strats p ->
  match strats with
  | []             -> assert false
  | S_Unif    :: l -> solve_unifs l p
  | S_Whnf    :: l -> solve_whnfs l p
  | (S_Loop(l) as s) :: _ -> solve (l @ [s]) p
  | S_Done    :: l ->
      if is_done p then
        if p.unsolved = [] then []
        else if p.recompute then
          begin
            let problems = {no_problems with unif_problems = p.unsolved} in
            solve (S_Unif::strats) problems
          end
        else p.unsolved
      else solve l p

(** [solve_unifs s p] tries to solve the unification problems of
    [p]. Then, it continues with the remaining problems following the
    strategy list [s]. *)
and solve_unifs : strategy -> problems -> unif list = fun strat p ->
  match p.unif_problems with
  | []       -> solve strat p
  | (t,u)::l -> solve_unif t u strat {p with unif_problems = l}

(** [solve_whnfs s p] tries to solve the unification problems of [p]
    that msut be weak-head-normalized first. Then, it continues with
    the remaining problems following the strategy list [s]. *)
and solve_whnfs : strategy -> problems -> unif list = fun strat p ->
  match p.whnf_problems with
  | []       -> solve strat p
  | (t,u)::l -> solve_whnf t u strat {p with whnf_problems = l}

(** [solve_unif t1 t2 s p] tries to solve the unificaton problem
    [(t1,t2)]. Then, it continues with the remaining problems
    following the strategy list [s]. *)
and solve_unif t1 t2 strats p : unif list =
  if t1 == t2 then solve_unifs strats p
  else
    begin
      if !log_enabled then log_solv "solving [%a] ~ [%a]" pp t1 pp t2;
      match unfold t1, unfold t2 with
      | Type, Type
      | Kind, Kind -> solve (S_Unif::strats) p

      | Vari x, Vari y when Bindlib.eq_vars x y -> solve (S_Unif::strats) p

      | Prod(a,f), Prod(b,g) | Abst(a,f), Abst(b,g) ->
         let (_,u,v) = Bindlib.unbind2 f g in
         let unif_problems = (a,b) :: (u,v) :: p.unif_problems in
         solve (S_Unif::strats) {p with unif_problems}

      | Symb(s1), Symb(s2) when s1 == s2 -> solve (S_Unif::strats) p

      | Meta(m1,a1), Meta(m2,a2)
        when m1==m2 && Array.for_all2 eq_vari a1 a2 ->
         solve (S_Unif::strats) p

      | Meta(m,ts), v when instantiate m ts v ->
          solve (S_Unif::strats) {p with recompute = true}
      | v, Meta(m,ts) when instantiate m ts v ->
          solve (S_Unif::strats) {p with recompute = true}

      | (Symb(s)  , _        ) when not (Sign.is_const s) ->
          let whnf_problems = (t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | (_        , Symb(s)  ) when not (Sign.is_const s) ->
          let whnf_problems = (t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | (Meta(_,_), _        )
      | (_        , Meta(_,_))
      | (Appl(_,_), _        )
      | (_        , Appl(_,_)) ->
          let whnf_problems = (t1,t2) :: p.whnf_problems in
          solve (S_Unif::strats) {p with whnf_problems}

      | (_        , _        ) ->
          fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
    end

(** [solve_whnf t1 t2 s p] tries to solve the unificaton problem
    [(t1,t2)] by first weak-head-normalizing it first. Then, it
    continues with the remaining problems following the strategy list
    [s]. *)
and solve_whnf t1 t2 strats p : unif list =
  let (h1, ts1) = Eval.whnf_stk t1 [] in
  let (h2, ts2) = Eval.whnf_stk t2 [] in
  if !log_enabled then
    begin
      let t1 = Eval.to_term h1 ts1 in
      let t2 = Eval.to_term h2 ts2 in
      log_solv "solve_whnf [%a] [%a]" pp t1 pp t2;
    end;
  match h1, h2 with
  | Type, Type
  | Kind, Kind -> solve (S_Whnf::strats) p
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

  | Vari x, Vari y when Bindlib.eq_vars x y && List.same_length ts1 ts2 ->
      let unif_problems =
        let fn l t1 t2 = Pervasives.(snd !t1, snd !t2)::l in
        List.fold_left2 fn p.unif_problems ts1 ts2
      in
      solve (S_Whnf::strats) {p with unif_problems}

  | Prod(a,f), Prod(b,g)
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
  | Abst(a,f), Abst(b,g) ->
  (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
     let (_,u,v) = Bindlib.unbind2 f g in
     let unif_problems = (a,b) :: (u,v) :: p.unif_problems in
     solve (S_Unif::S_Whnf::strats) {p with unif_problems}

  | Symb(s1), Symb(s2) when s1 == s2 && ts1 = [] && ts2 = [] ->
     solve (S_Whnf::strats) p

  | Symb(s1), Symb(s2) when Sign.is_const s1 && Sign.is_const s2 ->
     if s1 == s2 && List.same_length ts1 ts2 then
       let unif_problems =
        let fn l t1 t2 = Pervasives.(snd !t1, snd !t2)::l in
        List.fold_left2 fn p.unif_problems ts1 ts2
       in
       solve (S_Unif::S_Whnf::strats) {p with unif_problems}
     else fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2

  | Meta(m1,a1), Meta(m2,a2)
    when m1 == m2 && ts1 = [] && ts2 = [] && Array.for_all2 eq_vari a1 a2 ->
     solve (S_Whnf::strats) p

  | Meta(m,ts), _ when ts1 = [] && instantiate m ts t2 ->
      solve (S_Whnf::strats) {p with recompute = true}
  | _, Meta(m,ts) when ts2 = [] && instantiate m ts t1 ->
      solve (S_Whnf::strats) {p with recompute = true}

  | Meta(_,_), _
  | _, Meta(_,_) ->
      solve (S_Whnf::strats) {p with unsolved = (t1,t2) :: p.unsolved}

  | Symb(s), _ when not (Sign.is_const s) ->
     if Eval.eq_modulo t1 t2 then solve (S_Whnf::strats) p
     else solve (S_Whnf::strats) {p with unsolved = (t1,t2) :: p.unsolved}

  | _, Symb(s) when not (Sign.is_const s) ->
     if Eval.eq_modulo t1 t2 then solve (S_Whnf::strats) p
     else solve (S_Whnf::strats) {p with unsolved = (t1,t2) :: p.unsolved}

  | (_        , _        ) ->
     fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2

(** [solve b strats p] sets [can_instantiate] to [b] and returns
    [Some(l)] if [solve strats p] returns [l], and [None] otherwise. *)
let solve : bool -> strategy -> problems -> unif list option = fun b s p ->
  can_instantiate := b;
  try Some (solve s p) with Fatal(_,m) ->
    if !log_enabled then log_solv (red "solve: %s.\n") m; None

let msg (a,b) =
  if !log_enabled then log_solv "Cannot solve [%a] ~ [%a]\n" pp a pp b

(** [has_type c t u] returns [true] iff [t] has type [u] in context [c]. *)
let check : Ctxt.t -> term -> term -> bool = fun c t a ->
  if !log_enabled then log_solv "check [%a] [%a]" pp t pp a;
  let unif_problems = Typing.check c t a in
  let problems = {no_problems with unif_problems} in
  match solve true default_strategy problems with
  | Some l -> List.iter msg l; l = []
  | None   -> false

(** [has_type_with_constrs cs c t u] returns [true] iff [t] has type
    [u] in context [c] and constraints [cs] without instantiating any
    user-defined metavariable. *)
let check_with_constr (cs:unif list) (t:term) (a:term) : unit =
  if !log_enabled then log_solv "check_with_constr [%a] [%a]" pp t pp a;
  let unif_problems = Typing.check Ctxt.empty t a in
  let problems = {no_problems with unif_problems} in
  match solve false default_strategy problems with
  | Some l -> let l = List.filter (fun x -> not (List.mem x cs)) l in
              List.iter msg l;
              if not (l = []) then fatal_no_pos "Unsatisfied constraints."
  | None   -> fatal_no_pos "Unsatisfiable constraints."

(** [infer_constr c t] returns a pair [a,l] where [l] is a list
    of unification problems for [a] to be the type of [t] in context [c]. *)
let infer_constr (c:Ctxt.t) (t:term) : unif list * term =
  if !log_enabled then log_solv "infer_constr [%a]" pp t;
  let (a, unif_problems) = Typing.infer c t in
  let problems = {no_problems with unif_problems} in
  match solve true default_strategy problems with
  | Some(l) -> (l, a)
  | None    -> fatal_no_pos "FIXME1."

(** [infer c t] returns [Some u] if [t] has type [u] in context [c],
    and [None] otherwise. *)
let infer (c:Ctxt.t) (t:term) : term option =
  let l, a = infer_constr c t in
  if l = [] then Some a else (List.iter msg l; None)

(** [sort_type c t] returns [true] iff [t] has type a sort in context [c]. *)
let sort_type (c:Ctxt.t) (t:term) : unit =
  if !log_enabled then log_solv "sort_type [%a]" pp t;
  match infer c t with
  | Some(a) ->
      begin
        match unfold a with
        | Type
        | Kind -> ()
        | a    -> fatal_no_pos "[%a] has type [%a] (not a sort)." pp t pp a
      end
  | None    -> fatal_no_pos "Unable to infer a sort for [%a]." pp t
