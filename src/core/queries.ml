(** Queries (available in tactics and at the toplevel). *)

open Console
open Pos
open Syntax
open Unif
open Terms
open Print

(** [handle_query ss ps q] *)
let handle_query : Sig_state.t -> Proof.t option -> p_query -> unit =
  fun ss ps q ->
  let env =
    match ps with
    | None     -> Env.empty
    | Some(ps) -> fst (Proof.focus_goal q.pos ps)
  in
  let ctxt = Env.to_ctxt env in
  let scope = Scope.scope_term Public ss env in
  match q.elt with
  | P_query_assert(must_fail, asrt)  ->
      begin
      match asrt with
      | P_assert_typing(pt,pa) ->
          begin
            let t = scope pt and a = scope pa in
            out 1 "(asrt) it is %b that %a\n" (not must_fail)
              pp_typing (ctxt, t, a);
          (* Check that [a] is typable by a sort. *)
          match Infer.infer ctxt a with
          | None -> fatal q.pos "[%a] is not typable." pp_term a
          | Some(sort, to_solve) ->
          match solve_noexn {empty_problem with to_solve} with
          | None -> fatal q.pos "[%a] is not typable." pp_term a
          | Some ((_::_) as cs) ->
              List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
              fatal q.pos "[%a] may be not typable." pp_term a
          | Some [] ->
          match unfold sort with
          | Type | Kind ->
              (* Check that [t] is of type [a]. *)
              let result =
                match Infer.check ctxt t a with
                | None -> false
                | Some to_solve ->
                    match solve_noexn {empty_problem with to_solve} with
                    | None -> false
                    | Some cs ->
                        List.iter
                          (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
                        cs = []
              in
              if result = must_fail then fatal q.pos "Assertion failed."
          | _ -> fatal q.pos "[%a] has type [%a] and not a sort."
                   pp_term a pp_term sort
          end
      | P_assert_conv(pt,pu)   ->
          begin
          let t = scope pt and u = scope pu in
          out 1 "(asrt) it is %b that %a\n" (not must_fail)
            pp_constr (ctxt, t, u);
          (* Check that [t] is typable. *)
          match Infer.infer ctxt t with
          | None -> fatal q.pos "[%a] is not typable." pp_term t
          | Some(a, to_solve) ->
          match Unif.(solve_noexn {empty_problem with to_solve}) with
          | None -> fatal q.pos "[%a] is not typable." pp_term t
          | Some ((_::_) as cs) ->
              List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
              fatal q.pos "[%a] may be not typable." pp_term t
          | Some [] ->
          (* Check that [u] is typable. *)
          match Infer.infer ctxt u with
          | None -> fatal q.pos "[%a] is not typable." pp_term u
          | Some(b, to_solve) ->
          match Unif.(solve_noexn {empty_problem with to_solve}) with
          | None -> fatal q.pos "[%a] is not typable." pp_term u
          | Some ((_::_) as cs) ->
              List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
              fatal q.pos "[%a] may be not typable." pp_term u
          | Some [] ->
          (* Check that [t] and [u] have the same type. *)
          match solve_noexn {empty_problem with to_solve = [ctxt,a,b]} with
          | None ->
              fatal q.pos "[%a] has type [%a]\n[%a] has type [%a]\n\
                         The two types are not unifiable."
                pp_term t pp_term a pp_term u pp_term b
          | Some ((_::_) as cs) ->
              List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
              fatal q.pos "[%a] has type [%a]\n[%a] has type [%a]\n\
                         The two types are not unifiable."
                pp_term t pp_term a pp_term u pp_term b
          | Some [] ->
              if Eval.eq_modulo ctxt t u = must_fail then
                fatal q.pos "Assertion failed."
          end
      end
  | P_query_debug(e,s)     ->
      (* Just update the option, state not modified. *)
      Console.set_debug e s;
      out 3 "(flag) debug → %s%s\n" (if e then "+" else "-") s
  | P_query_verbose(i)     ->
      (* Just update the option, state not modified. *)
      if Timed.(!Console.verbose) = 0 then
        (Timed.(Console.verbose := i); out 1 "(flag) verbose → %i\n" i)
      else
        (out 1 "(flag) verbose → %i\n" i; Timed.(Console.verbose := i))
  | P_query_flag(id,b)     ->
      (* We set the value of the flag, if it exists. *)
      begin
        try Console.set_flag id b with Not_found ->
          wrn q.pos "Unknown flag \"%s\"." id
      end;
      out 3 "(flag) %s → %b\n" id b
  | P_query_infer(pt, cfg) ->
      (* Infer the type of [t]. *)
      begin
      let t = scope pt in
      match Infer.infer ctxt t with
      | None -> fatal pt.pos "[%a] is not typable." pp_term t
      | Some(a, to_solve) ->
      match solve_noexn {empty_problem with to_solve} with
      | None -> fatal q.pos "[%a] is not typable." pp_term t
      | Some ((_::_) as cs) ->
          List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
          fatal q.pos "[%a] is not typable." pp_term t
      | Some [] ->
          out 1 "(infr) %a : %a\n" pp_term t pp_term (Eval.eval cfg ctxt a)
      end
  | P_query_normalize(pt, cfg)        ->
      (* Normalize [t]. *)
      begin
      let t = scope pt in
      match Infer.infer ctxt t with
      | None -> fatal pt.pos "[%a] is not typable." pp_term t
      | Some(a, to_solve) ->
      match solve_noexn {empty_problem with to_solve} with
      | None -> fatal q.pos "[%a] is not typable." pp_term t
      | Some ((_::_) as cs) ->
          List.iter (wrn q.pos "Cannot solve [%a].\n" pp_constr) cs;
          fatal q.pos "[%a] is not typable." pp_term t
      | Some [] ->
          out 1 "(comp) %a\n" pp_term (Eval.eval cfg ctxt t)
      end
  | P_query_prover(s)      ->
      Timed.(Why3_tactic.default_prover := s)
  | P_query_prover_timeout(n)->
      Timed.(Why3_tactic.timeout := n)
