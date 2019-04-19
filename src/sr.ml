(** Type-checking and inference. *)

open Timed
open Console
open Print
open Extra
open Terms
open Basics

(** Logging function for typing. *)
let log_subj =
  new_logger 'j' "subj" "debugging information for subject-reduction"
let log_subj = log_subj.logger

(** [check_rule symbs builtins r] check whether rule [r] is well-typed. The
    program fails gracefully in case of error. *)
let check_rule :
  sym StrMap.t -> sym * pp_hint * rule Pos.loc -> unit
  = fun builtins (s,h,r) ->
  if !log_enabled then log_subj "check_rule [%a]" pp_rule (s, h, r.elt);
  (* We process the LHS to replace pattern variables by fresh function
     symbols. *)
  let lhs, rhs = to_terms_closed (s, r.elt) in
  (* Infer the type of the LHS and the constraints. *)
  match Typing.infer_constr builtins Ctxt.empty lhs with
  | None                       -> wrn r.pos "Untypable LHS."
  | Some (lhs_constrs, ty_lhs) ->
      if !log_enabled then
        begin
          log_subj "LHS has type [%a]" pp ty_lhs;
          let fn (t, u) = log_subj "  if [%a] ~ [%a]" pp t pp u in
          List.iter fn lhs_constrs
        end;
      let ord s1 s2 = Pervasives.compare s1.sym_name s2.sym_name in
      let t1 = Time.save () in
      let check_fo (t, u) = Basics.check_fo t; Basics.check_fo u in
      try
        List.iter check_fo lhs_constrs;
        let rules_to_add = Completion.completion lhs_constrs ord in
        Time.restore t1;
        List.iter
          (fun (s, rs) -> s.sym_rules := rs @ !(s.sym_rules)) rules_to_add;
        (* Check that the RHS has the same type as the LHS. *)
        let to_solve = Infer.check Ctxt.empty rhs ty_lhs in
        match Unif.(solve builtins false {no_problems with to_solve}) with
        | Some cs ->
            if cs <> [] then
              begin
                let fn (t, u) =
                  fatal_msg "Cannot solve [%a] ~ [%a]\n" pp t pp u in
                List.iter fn cs;
                fatal r.pos  "Unable to prove SR for rule [%a]."
                pp_rule (s, h, r.elt)
              end
            else Time.restore t1
        | None    ->
            fatal r.pos "Rule [%a] does not preserve typing."
            pp_rule (s, h, r.elt)
      with Not_FO ->
        wrn r.pos "Rule [%a] may not preserve typing." pp_rule (s, h, r.elt)
