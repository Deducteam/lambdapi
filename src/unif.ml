(** Solving unification constraints. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print

(** Logging function for unification. *)
let log_solv = new_logger 's' "solv" "debugging information for unification"
let log_solv = log_solv.logger

(** Representation of a set of problems. *)
type problems =
  { to_solve  : unif_constrs
  (** List of unification problems to solve. *)
  ; unsolved  : unif_constrs
  (** List of unification problems that could not be solved. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Empty problem. *)
let no_problems : problems =
  {to_solve  = []; unsolved = []; recompute = false}

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** [nl_distinct_vars ts] checks that [ts] is made of variables [vs] only
   and returns some copy of [vs] where variables occurring more than
   once are replaced by fresh variables. It returns [None]
   otherwise. *)
let nl_distinct_vars : term array -> tvar array option =
  let exception Not_a_var in fun ts ->
  let open Pervasives in
  let vars = ref VarSet.empty
  and nl_vars = ref VarSet.empty in
  let to_var t =
    match unfold t with
    | Vari x ->
       begin
         if VarSet.mem x !vars then nl_vars := VarSet.add x !nl_vars
         else vars := VarSet.add x !vars;
         x
       end
    | _ -> raise Not_a_var
  in
  let replace_nl_var x =
    if VarSet.mem x !nl_vars then Bindlib.new_var mkfree "_" else x
  in
  try Some (Array.map replace_nl_var (Array.map to_var ts))
  with Not_a_var -> None

(** [instantiate m ts u] check whether [m] can be instantiated for solving the
    unification problem “m[ts] = u”. The returned boolean tells whether [m]
    was instantiated or not. *)
let instantiate : meta -> term array -> term -> bool = fun m ts u ->
  (!can_instantiate || internal m)
  && not (occurs m u)
  && match nl_distinct_vars ts with
     | None -> false
     | Some vs ->
        let bu = Bindlib.bind_mvar vs (lift u) in
        Bindlib.is_closed bu (* To make sure that there is no non-linear
                                variable of [vs] occurring in [u]. *)
        && (set_meta m (Bindlib.unbox bu); true)

(** [solve p] tries to solve the unification problems of [p] and
   returns the constraints that could not be solved. *)
let rec solve : problems -> unif_constrs = fun p ->
  match p with
  | { to_solve = []; unsolved = []; _ } -> []
  | { to_solve = []; unsolved = cs; recompute = true } ->
     solve {no_problems with to_solve = cs}
  | { to_solve = []; unsolved = cs; _ } -> cs
  | { to_solve = (t,u)::to_solve; _ } -> solve_aux t u {p with to_solve}

(** [solve_aux t1 t2 p] tries to solve the unificaton problem given by [p] and
    the constraint [(t1,t2)], starting with the latter. *)
and solve_aux : term -> term -> problems -> unif_constrs = fun t1 t2 p ->
  let (h1, ts1) = Eval.whnf_stk t1 [] in
  let (h2, ts2) = Eval.whnf_stk t2 [] in
  if !log_enabled then
    begin
      let t1 = Eval.to_term h1 ts1 in
      let t2 = Eval.to_term h2 ts2 in
      log_solv "solve [%a] [%a]" pp t1 pp t2;
    end;

  let add_to_unsolved () =
    let t1 = Eval.to_term h1 ts1 in
    let t2 = Eval.to_term h2 ts2 in
    if Eval.eq_modulo t1 t2 then solve p
    else solve {p with unsolved = (t1,t2) :: p.unsolved}
  in
  let error () =
    let t1 = Eval.to_term h1 ts1 in
    let t2 = Eval.to_term h2 ts2 in
    fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
  in
  let decompose () =
    let add_args =
      List.fold_left2 (fun l p1 p2 -> Pervasives.((snd !p1, snd !p2)::l)) in
    let to_solve =
      try add_args p.to_solve ts1 ts2 with Invalid_argument _ -> error () in
    solve {p with to_solve}
  in

  (* For a problem m[vs]=s(ts), where [vs] are distinct variables, m
     is a meta of type ∀y0:a0,..,∀yk-1:ak-1,b (k = length vs), s is an
     injective symbol of type ∀x0:b0,..,∀xn-1:bn-1,c (n = length ts),
     we instantiate m by s(m0[vs],..,mn-1[vs]) where mi is a fresh
     meta of type ∀v0:a0,..,∀vk-1:ak-1{y0=v0,..,yk-2=vk-2},
     bi{x0=m0[vs],..,xi-1=mi-1[vs]}. *)
  let imitate m vs us s h ts =
    let exception Unsolvable in try
    if not (us = [] && Sign.is_inj s) then raise Unsolvable;
    let vars = match distinct_vars_opt vs with
      | None -> raise Unsolvable
      | Some vars -> vars
    in
    (* Build the environment (yk-1, ak-1{y0=v0,..,yk-2=vk-2}), .., (y0, a0). *)
    let env = Env.of_prod vars !(m.meta_type) in
    (* Build the term s(m0[vs],..,mn-1[vs]). *)
    let k = Array.length vars in
    let t =
      let rec build i acc t =
        if i <= 0 then Basics.add_args (Symb(s,h)) (List.rev acc)
        else match unfold t with
             | Prod(a,b) ->
                let m = fresh_meta (Env.to_prod env (lift a)) k in
                let u = Meta (m,vs) in
                build (i-1) (u::acc) (Bindlib.subst b u)
             | _ -> raise Unsolvable
      in build (List.length ts) [] !(s.sym_type)
    in
    set_meta m (Bindlib.unbox (Bindlib.bind_mvar vars (lift t)));
    solve_aux t1 t2 p
    with Unsolvable -> add_to_unsolved ()
  in

  match (h1, h2) with
  (* Cases in which [ts1] and [ts2] must be empty due to typing / whnf. *)
  | (Type       , Type       )
  | (Kind       , Kind       ) -> solve p

  | (Prod(a1,b1), Prod(a2,b2))
  | (Abst(a1,b1), Abst(a2,b2)) ->
     let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
     solve_aux a1 a2 {p with to_solve = (b1,b2) :: p.to_solve}

  (* Other cases. *)
  | (Vari(x1)   , Vari(x2)   ) ->
     if Bindlib.eq_vars x1 x2 then decompose () else error ()

  | (Symb(s1,_) , Symb(s2,_) ) ->
     if s1 == s2 then
       match s1.sym_mode with
       | Const -> decompose ()
       | Injec ->
          if List.same_length ts1 ts2 then decompose ()
          else if !(s1.sym_rules) = [] then error ()
          else add_to_unsolved ()
       | Defin ->
          if !(s1.sym_rules) <> [] || List.same_length ts1 ts2
          then add_to_unsolved ()
          else error ()
     else if !(s1.sym_rules) = [] && !(s2.sym_rules) = [] then error ()
     else add_to_unsolved ()

  | (Meta(m,ts) , _          ) when ts1 = [] && instantiate m ts t2 ->
      solve {p with recompute = true}
  | (_          , Meta(m,ts) ) when ts2 = [] && instantiate m ts t1 ->
      solve {p with recompute = true}

  | (Meta(m,ts)  , Symb(s,h) ) -> imitate m ts ts1 s h ts2
  | (Symb(s,h)  , Meta(m,ts) ) -> imitate m ts ts2 s h ts1

  | (Meta(_,_)  , _          )
  | (_          , Meta(_,_)  ) -> add_to_unsolved ()

  | (Symb(s,_)  , _          )
  | (_          , Symb(s,_)  ) ->
      if !(s.sym_rules) = [] then error () else add_to_unsolved ()

  | (_          , _          ) -> error ()

(** [solve flag problems] attempts to solve [problems],  after having sets the
    value of [can_instantiate] to [flag].  If there is no solution,  the value
    [None] is returned. Otherwise [Some(cs)] is returned,  where the list [cs]
    is a list of unsolved convertibility constraints. *)
let solve : bool -> problems -> unif_constrs option = fun b p ->
  can_instantiate := b;
  try Some (solve p) with Fatal(_,m) ->
    if !log_enabled then log_solv (red "solve: %s") m; None
