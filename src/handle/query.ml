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
open Base

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [return pp x] prints [x] using [pp] on [Stdlib.(!out_fmt)] at verbose
   level 1 and returns a function for printing [x] on a string using [pp]. *)
let return : 'a pp -> 'a -> result = fun pp x ->
  Console.out 1 (Extra.red "%a\n") pp x;
  Some (fun () -> Format.asprintf "%a" pp x)

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
        | Some ps -> return Proof.pp_goals ps
      end
  | P_query_print(Some qid) ->
      let pp_sym_info ppf s =
        let out = Format.fprintf in
        let open Timed in
        (* print its type and properties *)
        out ppf "%a%a%asymbol %a: %a\n" pp_expo s.sym_expo
          pp_prop s.sym_prop pp_match_strat s.sym_mstrat
          pp_sym s pp_prod (!(s.sym_type), s.sym_impl);
        (* print its definition *)
        begin
          match !(s.sym_def) with
          | Some t -> out ppf "\n≔ %a\n" pp_term t
          | None -> ()
        end;
        (* print its notation *)
        let pp_notation : Sign.notation option pp = fun ppf n ->
          match n with
          | None -> ()
          | Some n -> out ppf "notation %a %a" pp_sym s pp_notation n
        in
        pp_notation ppf (notation_of s);
        (* print its rules *)
        begin
          match !(s.sym_rules) with
          | [] -> ()
          | rs -> let pp_rule ppf r = out ppf "  %a\n" pp_rule (s,r) in
                  out ppf "rules:\n%a" (List.pp pp_rule "") rs
        end;
        (* print its constructors (if it is an inductive type) *)
        begin
          let open Sign in
          (* get the signature of [s] *)
          let sign =
            try Path.Map.find s.sym_path Timed.(!loaded)
            with Not_found -> assert false
          in
          let pp_decl : sym pp = fun ppf s ->
            out ppf "  %a: %a\n" pp_sym s pp_term !(s.sym_type) in
          let pp_ind : ind_data pp = fun ppf ind ->
            out ppf "constructors:\n%ainduction principle:\n%a"
              (List.pp pp_decl "") ind.ind_cons pp_decl ind.ind_prop in
          try out ppf "%a" pp_ind (SymMap.find s Timed.(!(sign.sign_ind)))
          with Not_found -> ()
        end;
      in
      return pp_sym_info (Sig_state.find_sym ~prt:true ~prv:true ss qid)
  | P_query_proofterm ->
      (match ps with
       | None -> fatal pos "Not in a proof"
       | Some ps ->
           match ps.proof_term with
           | Some m -> return pp_term (Meta(m,[||]))
           | None -> fatal pos "Not in a definition")
  | _ ->
  let env = Proof.focus_env ps in
  let sms = lazy
    (match ps with
    | None -> Extra.IntMap.empty
    | Some ps -> Proof.sys_metas ps)
  in
  let scope = Scope.scope_term true ss env sms in
  let ctxt = Env.to_ctxt env in
  let module Infer = (val Stdlib.(!Infer.default)) in
  match elt with
  | P_query_debug(_,_)
  | P_query_verbose(_)
  | P_query_flag(_,_)
  | P_query_prover(_)
  | P_query_prover_timeout(_)
  | P_query_print(_)
  | P_query_proofterm -> assert false (* already done *)
  | P_query_assert(must_fail, P_assert_typing(pt,pa)) ->
      let t = scope pt in let a = scope pa in
      Console.out 1 "(asrt) it is %b that %a\n" (not must_fail)
        pp_typing (ctxt, t, a);
      (* Check that [a] is typable by a sort. *)
      let (a, _) = Infer.check_sort ctxt {elt=a;pos=pa.pos} in
      let result =
        try ignore (Infer.check ?pos ctxt t a); true
        with Fatal _ -> false
      in
      if result = must_fail then fatal pos "Assertion failed.";
      None
  | P_query_assert(must_fail, P_assert_conv(pt,pu)) ->
      let t = scope pt in let u = scope pu in
      Console.out 1 "(asrt) it is %b that %a\n" (not must_fail)
        pp_constr (ctxt, t, u);
      (* Check that [t] is typable. *)
      let (t, a) = Infer.infer ctxt {elt=t;pos=pt.pos} in
      (* Check that [u] is typable. *)
      let (u, b) = Infer.infer ctxt {elt=u;pos=pu.pos} in
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
      let (_, a) = Infer.infer ctxt {elt=t;pos=pt.pos} in
      return pp_term (Eval.eval cfg ctxt a)
  | P_query_normalize(pt, cfg) ->
      let t = scope pt in
      let t, _ = Infer.infer ctxt {elt=t;pos=pt.pos} in
      return pp_term (Eval.eval cfg ctxt t)
