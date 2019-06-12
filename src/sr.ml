(** Type-checking and inference. *)

open Timed
open Console
open Terms
open Print
open Extra
open Basics
open Pos

(** Logging function for typing. *)
let log_subj =
  new_logger 'j' "subj" "debugging information for subject-reduction"
let log_subj = log_subj.logger

(** Representation of a substitution. *)
type subst = tvar array * term array

(** [subst_from_constrs cs] builds a //typing substitution// from the list  of
    constraints [cs]. The returned substitution is given by a couple of arrays
    [(xs,ts)] of the same length.  The array [xs] contains the variables to be
    substituted using the terms of [ts] at the same index. *)
let subst_from_constrs : (term * term) list -> subst = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []        -> List.split acc
    | (a,b)::cs ->
    let (ha,argsa) = Basics.get_args a in
    let (hb,argsb) = Basics.get_args b in
    let na = List.length argsa in
    let nb = List.length argsb in
    match (unfold ha, unfold hb) with
    | (Symb(sa,_), Symb(sb,_)) when sa == sb && na = nb && Sign.is_inj sa ->
        let fn l t1 t2 = (t1,t2) :: l in
        build_sub acc (List.fold_left2 fn cs argsa argsb)
    | (Vari(x)   , _         ) when argsa = [] -> build_sub ((x,b)::acc) cs
    | (_         , Vari(x)   ) when argsb = [] -> build_sub ((x,a)::acc) cs
    | (_         , _         )                 -> build_sub acc cs
  in
  let (vs,ts) = build_sub [] cs in
  (Array.of_list vs, Array.of_list ts)

(** Logging functions and error messages *)
let typ_cond s t conds =
  log_subj "%s has type [%a]" s pp t;
  let fn (t, u) = log_subj " if [%a] ~ [%a]" pp t pp u in
  List.iter fn conds

let unsolved_msg (t, u) = fatal_msg "Cannot solve [%a] ~ [%a]\n" pp t pp u

let sr_unproved_msg (s, h, r) =
  fatal r.pos "Unable to prove SR for rule [%a]." pp_rule (s, h, r.elt)

let sr_not_preserved_msg (s, h, r) =
  fatal r.pos "Rule [%a] may not preserve typing." pp_rule (s, h, r.elt)

(** [check_eq eq eqs] checks if there exists an equation [eq'] in [eqs] such
    that (t_i == u_i (or u_(1-i)) for i = 0, 1) where [eq] = (t_0, t_1)
    and [eq'] = (u_0, u_1). *)
let check_eq eq eqs =
  let eq_comm (t0, t1) (u0, u1) =
    (Eval.eq_modulo t0 u0 && Eval.eq_modulo t1 u1) ||
    (Eval.eq_modulo t1 u0 && Eval.eq_modulo t0 u1)
  in
  List.exists (eq_comm eq) eqs

(** [check_rule builtins (s, h, r)] checks whether rule [r] is well-typed. The
    program fails gracefully in case of error. *)
let check_rule :
  sym StrMap.t -> sym * pp_hint * rule Pos.loc -> unit
  = fun builtins (s,h,r) ->
  let lhs, rhs = replace_patt_by_meta_rule (s, r.elt) in
  match Typing.infer_constr builtins Ctxt.empty lhs with
  | None                       -> wrn r.pos "Untypable LHS"
  | Some (lhs_constrs, ty_lhs) ->
      let t0 = Time.save () in
      if !log_enabled then typ_cond "LHS" ty_lhs lhs_constrs;
      try
        let constrs = Unif.add_rules_from_constrs lhs_constrs in
        (* Check that the RHS has the same type as the LHS. *)
        let to_solve = Infer.check Ctxt.empty rhs ty_lhs in
        match Unif.(solve builtins false {no_problems with to_solve}) with
        | Some cs ->
            if cs <> [] then
              let cs = List.filter (fun c -> not (check_eq c constrs)) cs in
              if cs <> [] then raise Non_nullary_meta
              else Time.restore t0
            else Time.restore t0
        | None    -> sr_not_preserved_msg (s, h, r)
      with Non_nullary_meta ->
        Time.restore t0;
        let (xs, ts) = subst_from_constrs lhs_constrs in
        let p = Bindlib.box_pair (lift rhs) (lift ty_lhs) in
        let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
        let (rhs, ty_lhs) = Bindlib.msubst p ts in
        let to_solve = Infer.check Ctxt.empty rhs ty_lhs in
        if !log_enabled && to_solve <> [] then
          typ_cond "RHS" ty_lhs to_solve;
        let problems = Unif.{no_problems with to_solve} in
        match Unif.(solve builtins false problems) with
        | Some cs ->
            let cs = List.filter (fun c -> not (check_eq c lhs_constrs)) cs in
            if cs <> [] then
              begin
                List.iter unsolved_msg cs;
                sr_unproved_msg (s, h, r)
              end
            else Time.restore t0
        | None    ->
            sr_not_preserved_msg (s, h, r)
