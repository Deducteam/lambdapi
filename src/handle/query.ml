(** Query (available in tactics and at the toplevel). *)

open Common
open Error
open Pos
open Parsing
open Syntax
open Core
open Term
open Print
open Proof
open Debug
open! Lplib
open Extra

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [handle_query ss ps q] *)
let handle : Sig_state.t -> proof_state option -> p_query -> result =
  fun ss ps {elt;pos} ->
  match elt with
  | P_query_debug(e,s) ->
      set_debug e s;
      Console.out 3 "(flag) debug → %s%s\n" (if e then "+" else "-") s;
      None
  | P_query_verbose(i) ->
      if Timed.(!Console.verbose) = 0 then
        (Timed.(Console.verbose := i);
         Console.out 1 "(flag) verbose → %i\n" i)
      else
        (Console.out 1 "(flag) verbose → %i\n" i;
         Timed.(Console.verbose := i));
      None
  | P_query_flag(id,b) ->
      (try Console.set_flag id b
       with Not_found -> fatal pos "Unknown flag \"%s\"." id);
      Console.out 3 "(flag) %s → %b\n" id b;
      None
  | P_query_prover(s) -> Timed.(Why3_tactic.default_prover := s); None
  | P_query_prover_timeout(n) -> Timed.(Why3_tactic.timeout := n); None
  | P_query_print(None) ->
      begin
        match ps with
        | None -> fatal pos "Not in a proof."
        | Some ps -> Console.out 1 "%a" Proof.pp_goals ps;
                     Some (fun () -> Format.asprintf "%a" Proof.pp_goals ps)
      end
  | P_query_print(Some qid) ->
      let sym = Sig_state.find_sym ~prt:true ~prv:true ss qid in
      let open Timed in
      Console.out 1 "(prnt) %a%a%asymbol %a: %a" Tags.pp_expo sym.sym_expo
        Tags.pp_prop sym.sym_prop Tags.pp_match_strat !(sym.sym_mstrat)
        pp_sym sym pp_term !(sym.sym_type);
      Option.iter (fun h -> Console.out 1 " [%a]" pp_notation h)
        (notation_of sym);
      begin
        match !(sym.sym_def) with
        | Some t ->
            Console.out 1 " ≔ %a\n" pp_term t;
            Some (fun () -> Format.asprintf " ≔ %a" pp_term t)
        | None ->
            Console.out 1 "\n";
            let rule oc r = Format.fprintf oc "%a\n" pp_rule (sym, r) in
            Console.out 1 "%a" (List.pp rule "") !(sym.sym_rules);
            Some (fun () ->
                Format.asprintf "%a" (List.pp rule "") !(sym.sym_rules))
      end
  | P_query_proofterm ->
      (match ps with
       | None -> fatal pos "Not in a proof"
       | Some ps ->
           match ps.proof_term with
           | Some m ->
              Console.out 1 "%a\n" pp_term (Meta(m,[||]));
              Some (fun () -> Format.asprintf "%a" pp_term (Meta(m,[||])))
           | None -> fatal pos "Not in a definition")
  | _ ->
  let env = Proof.focus_env ps in
  let sms =
    match ps with
    | None -> IntMap.empty
    | Some ps -> Proof.sys_metas ps
  in
  let scope = Scope.scope_term Public ss env sms in
  let ctxt = Env.to_ctxt env in
  match elt with
  | P_query_debug(_,_)
  | P_query_verbose(_)
  | P_query_flag(_,_)
  | P_query_prover(_)
  | P_query_prover_timeout(_)
  | P_query_print(_)
  | P_query_proofterm -> assert false (* already done *)
  | P_query_assert(must_fail, P_assert_typing(pt,pa)) ->
      let t = scope pt and a = scope pa in
      Console.out 1 "(asrt) it is %b that %a\n" (not must_fail)
        pp_typing (ctxt, t, a);
      (* Check that [a] is typable by a sort. *)
      Infer.check_sort Unif.solve_noexn pos ctxt a;
      let result =
        try Infer.check Unif.solve_noexn pos ctxt t a; true
        with Fatal _ -> false
      in
      if result = must_fail then fatal pos "Assertion failed.";
      None
  | P_query_assert(must_fail, P_assert_conv(pt,pu)) ->
      let t = scope pt and u = scope pu in
      Console.out 1 "(asrt) it is %b that %a\n" (not must_fail)
        pp_constr (ctxt, t, u);
      (* Check that [t] is typable. *)
      let a = Infer.infer Unif.solve_noexn pt.pos ctxt t in
      (* Check that [u] is typable. *)
      let b = Infer.infer Unif.solve_noexn pu.pos ctxt u in
      (* Check that [t] and [u] have the same type. *)
      let to_solve = [ctxt,a,b] in
      begin
        match Unif.(solve_noexn {empty_problem with to_solve}) with
        | None ->
            fatal pos "[%a] has type [%a].\n[%a] has type [%a].\n\
                       Those two types are not unifiable."
              pp_term t pp_term a pp_term u pp_term b
        | Some ((_::_) as cs) ->
            List.iter (wrn pos "Cannot solve [%a].\n" pp_constr) cs;
            fatal pos "[%a] has type [%a]\n[%a] has type [%a]\n\
                       Those two types are not unifiable."
              pp_term t pp_term a pp_term u pp_term b
        | Some [] ->
            if Eval.eq_modulo ctxt t u = must_fail then
              fatal pos "Assertion failed."
      end;
      None
  | P_query_infer(pt, cfg) ->
      let t = scope pt in
      let a = Infer.infer Unif.solve_noexn pt.pos ctxt t in
      let res = Eval.eval cfg ctxt a in
      Console.out 1 "(infr) %a : %a\n" pp_term t pp_term res;
      Some (fun () -> Format.asprintf "%a : %a" pp_term t pp_term res)
  | P_query_normalize(pt, cfg) ->
      let t = scope pt in
      ignore (Infer.infer Unif.solve_noexn pt.pos ctxt t);
      Console.out 1 "(comp) %a\n" pp_term (Eval.eval cfg ctxt t);
      Some (fun () -> Format.asprintf "%a" pp_term (Eval.eval cfg ctxt t))
