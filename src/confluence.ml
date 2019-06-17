(** First-order syntactic unification *)

open Terms
open Basics
open Timed

exception Unsolvable

(** [unif_aux t1 t2 eqs] attempts to solve the first-order unification
    problem [(t1 = t2) :: eqs]. *)
let rec unif_aux : term -> term -> unif_constrs -> unit = fun t1 t2 eqs ->
  match (t1, t2) with
  | Type, Type
  | Kind, Kind                    -> unif eqs
  | Symb(s1, _), Symb(s2, _)      ->
      if s1 == s2 then unif eqs else raise Unsolvable
  | Vari _, _
  | _, Vari _
  | Prod _, _
  | _, Prod _
  | Abst _, _
  | _, Abst _                     -> assert false
  | Appl (t1, u1), Appl (t2, u2)  -> unif ((t1, t2) :: (u1, u2) :: eqs)
  | Meta (m1, [||]), Meta (_, [||]) ->
      let vs = Bindlib.new_mvar mkfree [||] in
      let bt2 = Bindlib.bind_mvar vs (lift t2) in
      set_meta m1 (Bindlib.unbox bt2);
      unif eqs
  | (Meta (m1, [||]), t2)
  | (t2, Meta (m1, [||]))          ->
      if occurs m1 t2 then raise Unsolvable
      else
        let vs = Bindlib.new_mvar mkfree [||] in
        let bt2 = Bindlib.bind_mvar vs (lift t2) in
        set_meta m1 (Bindlib.unbox bt2);
        unif eqs
  | _                             -> raise Unsolvable

(** [unif eqs] attempts to solve the unification problem [eqs]. *)
and unif : unif_constrs -> unit = fun eqs ->
  match eqs with
  | []              -> ()
  | (t1, t2) :: eqs -> unif_aux t1 t2 eqs

(** [cps rs] computes the critical pairs of the rewrite system [rs]. *)
let cps : (sym * rule) list -> (term * term) list = fun rs ->
  let acc = ref [] in
  let rs = List.map replace_patt_by_meta_rule rs in
  (* [cps_aux b r1 r2] computes the critical pairs between [r1] and [r2],
     where [b] indicates if the rules considered are different. *)
  let cps_aux : bool -> term * term -> term * term -> unit
    = fun b (lhs1, rhs1) (lhs2, rhs2) ->
    (* [find_cp t1 t2] computes the critical pairs between [r1] and [r2] by
       unifying [t1] and [t2], where [ti] is a subterm of the LHS of [ri]. *)
    let find_cp : term -> term -> unit = fun t1 t2 ->
      match (t1, t2) with
      | Meta _, _ -> ()
      | _, Meta _ -> ()
      | _         ->
          let reset_meta m = m.meta_value := None in
          iter_meta reset_meta lhs1;
          iter_meta reset_meta lhs2;
          try
            unif [(t1, t2)];
            acc := (rhs1, rhs2) :: !acc
          with Unsolvable -> () in
    let _, args1 = get_args lhs1 in
    let _, args2 = get_args lhs2 in
    find_cp lhs1 lhs2;
    List.iter (Basics.iter (find_cp lhs1)) args2;
    if b then List.iter (Basics.iter (fun t -> find_cp t lhs2)) args1 in
  let rec cps rs =
    match rs with
    | []       -> ()
    | r :: rs' -> begin
        List.iter (cps_aux true r) rs';
        cps_aux false r r;
        cps rs' end in
  cps rs;
  !acc
