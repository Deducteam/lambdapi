(** Type-checking and inference. *)

open Timed
open Console
open Print
open Extra
open Terms
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

let unsolved_msg (t, u) = fatal_msg "Cannot solve [%a] ~ [%a]\n" pp t pp u

let sr_unproved_msg (s, h, r) =
  fatal r.pos "Unable to prove SR for rule [%a]." pp_rule (s, h, r.elt)

let sr_not_preserved_msg (s, h, r) =
  fatal r.pos "Rule [%a] does not preserve typing." pp_rule (s, h, r.elt)

(** [check_rule symbs builtins r] check whether rule [r] is well-typed. The
    program fails gracefully in case of error. *)
let check_rule :
  sym StrMap.t -> sym * pp_hint * rule Pos.loc -> unit
  = fun builtins (s,h,r) ->
  try
    if !log_enabled then log_subj "check_rule [%a]" pp_rule (s, h, r.elt);
  (* We process the LHS to replace pattern variables by fresh function
     symbols. *)
    let lhs, rhs = to_closed_terms (s, r.elt) in
  (* Infer the type of the LHS and the constraints. *)
    match Typing.infer_constr builtins Ctxt.empty lhs with
    | None                       -> wrn r.pos "Untypable LHS."
    | Some (lhs_constrs, ty_lhs) ->
        if !log_enabled then
          begin
            log_subj "LHS has type [%a]" pp ty_lhs;
            let fn (t, u) = log_subj " if [%a] ~ [%a]" pp t pp u in
            List.iter fn lhs_constrs
          end;
        let ord s1 s2 = Pervasives.compare s1.sym_name s2.sym_name in
        let t1 = Time.save () in
        let check_fo (t, u) = Basics.check_fo t; Basics.check_fo u in
        List.iter check_fo lhs_constrs;
        let rules_to_add = Completion.completion lhs_constrs ord in
        Time.restore t1;
        List.iter
          (fun (s, rs) -> s.sym_rules := rs @ !(s.sym_rules)) rules_to_add;
        (* Check that the RHS has the same type as the LHS. *)
        let to_solve = Infer.check Ctxt.empty rhs ty_lhs in
        match Unif.(solve builtins false {no_problems with to_solve}) with
        | Some cs ->
            if cs <> [] then raise Not_FO
            else Time.restore t1
        | None    -> sr_not_preserved_msg (s, h, r)
  with Not_FO ->
    let lhs, rhs = to_terms (s, r.elt) in
    begin match Typing.infer_constr builtins Ctxt.empty lhs with
    | None                       -> wrn r.pos "Untypable LHS"
    | Some (lhs_constrs, ty_lhs) ->
        if !log_enabled then
          begin
            log_subj "LHS has type [%a]" pp ty_lhs;
            let fn (t, u) = log_subj " if [%a] ~ [%a]" pp t pp u in
            List.iter fn lhs_constrs
          end;
        let (xs, ts) = subst_from_constrs lhs_constrs in
        let p = Bindlib.box_pair (lift rhs) (lift ty_lhs) in
        let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
        let (rhs, ty_lhs) = Bindlib.msubst p ts in
        let to_solve = Infer.check Ctxt.empty rhs ty_lhs in
        if !log_enabled && to_solve <> [] then
          begin
            log_subj "RHS has type [%a]" pp ty_lhs;
            let fn (t, u) = log_subj " if [%a] ~ [%a]" pp t pp u in
            List.iter fn to_solve
          end;
        let problems = Unif.{no_problems with to_solve} in
        begin match Unif.(solve builtins false problems) with
        | Some cs ->
            let is_constr c =
              let eq_comm (t1, u1) (t2, u2) =
                (Eval.eq_modulo t1 t2 && Eval.eq_modulo u1 u2) ||
                (Eval.eq_modulo t1 u2 && Eval.eq_modulo t2 u1)
              in
              List.exists (eq_comm c) lhs_constrs
            in
            let cs = List.filter (fun c -> not (is_constr c)) cs in
            if cs <> [] then
              begin
                List.iter unsolved_msg cs;
                sr_unproved_msg (s, h, r)
              end
        | None    ->
            sr_not_preserved_msg (s, h, r)
        end
    end
