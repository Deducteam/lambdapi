(** Type-checking and inference. *)

open Extra
open Timed
open Console
open Terms
open Print
open Typing

(** Logging function for unification. *)
let log_solv = new_logger 's' "solv" "debugging information for unification"
let log_solv = log_solv.logger

(** Representation of a set of problems. *)
type problems =
  { to_solve  : conv_constrs
  (** List of unification problems that must be put in WHNF first. *)
  ; unsolved  : conv_constrs
  (** List of unsolved unification problems. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Empty problem. *)
let no_problems : problems =
  {to_solve  = []; unsolved = []; recompute = false}

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** [instantiate m ts v] check whether [m] can be instantiated to
    solve the unification problem [m[ts] = v]. Actually make the
    instantiation if it is possible. *)
let instantiate : meta -> term array -> term -> bool = fun m ar v ->
  (!can_instantiate || internal m) && distinct_vars ar && not (occurs m v) &&
  let bv = Bindlib.bind_mvar (to_tvars ar) (lift v) in
  Bindlib.is_closed bv && (set_meta m (Bindlib.unbox bv); true)

(** [solve p] tries to solve the unification problems of [p]. *)
let rec solve : problems -> conv_constrs = fun p ->
  match p.to_solve with
  | []       ->
     if p.unsolved = [] then []
     else if p.recompute then
       solve {no_problems with to_solve = p.unsolved}
     else p.unsolved
  | (t,u)::l -> solve_aux t u {p with to_solve = l}

(** [solve_aux t1 t2 p] tries to solve the unificaton problem
    [(t1,t2)]. Then, it continues with the remaining problems. *)
and solve_aux t1 t2 p : conv_constrs =
  let (h1, ts1) = Eval.whnf_stk t1 [] in
  let (h2, ts2) = Eval.whnf_stk t2 [] in
  if !log_enabled then
    begin
      let t1 = Eval.to_term h1 ts1 in
      let t2 = Eval.to_term h2 ts2 in
      log_solv "solve_aux [%a] [%a]" pp t1 pp t2;
    end;
  match h1, h2 with
  | Type, Type
  | Kind, Kind -> solve p
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)

  | Vari x, Vari y when Bindlib.eq_vars x y && List.same_length ts1 ts2 ->
      let to_solve =
        let fn l t1 t2 = Pervasives.(snd !t1, snd !t2)::l in
        List.fold_left2 fn p.to_solve ts1 ts2
      in
      solve {p with to_solve}

  | Prod(a,f), Prod(b,g)
  (* We have [ts1=ts2=[]] since [t1] and [t2] are [Kind] or typable. *)
  | Abst(a,f), Abst(b,g) ->
  (* We have [ts1=ts2=[]] since [t1] and [t2] are in whnf. *)
     let (_,u,v) = Bindlib.unbind2 f g in
     let to_solve = (a,b) :: (u,v) :: p.to_solve in
     solve {p with to_solve}

  | Symb(s1), Symb(s2) ->
     if s1 == s2 && Sign.is_inj s1 && List.same_length ts1 ts2 then
       let to_solve =
         let fn l t1 t2 = Pervasives.(snd !t1, snd !t2)::l in
         List.fold_left2 fn p.to_solve ts1 ts2
       in
       solve {p with to_solve}
     else
       let t1 = Eval.to_term h1 ts1
       and t2 = Eval.to_term h2 ts2 in
       if Eval.eq_modulo t1 t2 then solve p
       else solve {p with unsolved = (t1,t2) :: p.unsolved}

  | Meta(m1,a1), Meta(m2,a2)
       when m1 == m2 && Array.for_all2 eq_vari a1 a2
            && List.for_all2
                 (fun x y -> Pervasives.(Eval.eq_modulo (snd !x) (snd !y)))
                 ts1 ts2 ->
     solve p

  | Meta(m,ts), _ when ts1 = [] && instantiate m ts t2 ->
      solve {p with recompute = true}
  | _, Meta(m,ts) when ts2 = [] && instantiate m ts t1 ->
      solve {p with recompute = true}

  | Meta(_,_), _
  | _, Meta(_,_) ->
     let t1 = Eval.to_term h1 ts1
     and t2 = Eval.to_term h2 ts2 in
     solve {p with unsolved = (t1,t2) :: p.unsolved}

  | Symb(_), _
  | _, Symb(_) ->
     let t1 = Eval.to_term h1 ts1
     and t2 = Eval.to_term h2 ts2 in
     if Eval.eq_modulo t1 t2 then solve p
     else solve {p with unsolved = (t1,t2) :: p.unsolved}

  | (_        , _        ) ->
     fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2

(** [solve flag problems] attempts to solve [problems],  after having sets the
    value of [can_instantiate] to [flag].  If there is no solution,  the value
    [None] is returned. Otherwise [Some(cs)] is returned,  where the list [cs]
    is a list of unsolved convertibility constraints. *)
let solve : bool -> problems -> conv_constrs option = fun b p ->
  can_instantiate := b;
  try Some (solve p) with Fatal(_,m) ->
    if !log_enabled then log_solv (red "solve: %s.\n") m; None

(** [check ctx t a] tells whether [t] has type [a] in context [ctx]. *)
let check : Ctxt.t -> term -> term -> bool = fun ctx t a ->
  if !log_enabled then log_solv "check [%a] [%a]" pp t pp a;
  let to_solve = Typing.check ctx t a in
  match solve true {no_problems with to_solve} with
  | None     -> false
  | Some(cs) ->
      let fn (a,b) = log_solv "Cannot solve [%a] ~ [%a]\n" pp a pp b in
      if !log_enabled then List.iter fn cs; cs = []

(** [infer_constr ctx t] tries to infer a type [a],  together with unification
    constraints [cs], for the term [t] in context [ctx].  The function returns
    [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr : Ctxt.t -> term -> (conv_constrs*term) option = fun ctx t ->
  if !log_enabled then log_solv "infer_constr [%a]" pp t;
  let (a, to_solve) = Typing.infer ctx t in
  Option.map (fun cs -> (cs, a)) (solve true {no_problems with to_solve})

(** [infer ctx t] tries to infer a type [a] for [t] in the context [ctx].  The
    function returns [Some(a)] in case of success, and [None] otherwise. *)
let infer : Ctxt.t -> term -> term option = fun ctx t ->
  match infer_constr ctx t with
  | None       -> None
  | Some([],a) -> Some(a)
  | Some(cs,_) ->
      let fn (a,b) = log_solv "Cannot solve [%a] ~ [%a]\n" pp a pp b in
      if !log_enabled then List.iter fn cs; None

(** [sort_type ctx t] checks that the type of the term [t] in context [ctx] is
    a sort. If that is not the case, the exception [Fatal] is raised. *)
let sort_type : Ctxt.t -> term -> unit = fun ctx t ->
  if !log_enabled then log_solv "sort_type [%a]" pp t;
  match infer ctx t with
  | None    -> fatal_no_pos "Unable to infer a sort for [%a]." pp t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           -> fatal_no_pos "[%a] has type [%a] (not a sort)." pp t pp a
