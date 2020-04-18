(** Queries (available in tactics and at the toplevel). *)

open Console
open Pos
open Syntax
open Scope
open Unif
open Terms

(** [handle_query ss ps q] *)
let handle_query : sig_state -> Proof.t option -> p_query -> unit =
  fun ss ps q ->
  let pp = Print.pp_term ss in
  let pp_constr = Print.pp_constr ss in
  let env =
    match ps with
    | None     -> Env.empty
    | Some(ps) -> fst (Proof.focus_goal q.pos ps)
  in
  let scope = scope_term Public ss env in
  match q.elt with
  | P_query_assert(must_fail, asrt)  ->
      let result =
        match asrt with
        | P_assert_typing(pt,pa) ->
          let t = scope pt and a = scope pa and ctxt = Env.to_ctxt env in
          Typing.sort_type ss ctxt a;
          (try Typing.check ss ctxt t a with _ -> false)
        | P_assert_conv(pt,pu)   ->
          let t = scope pt and u = scope pu in
          let infer = Typing.infer ss (Env.to_ctxt env) in
          match (infer t, infer u) with
          | (Some(a), Some(b)) ->
              let pb = {empty_problem with to_solve = [[], a, b]} in
              begin
                match solve ss pb with
                | None -> fatal q.pos "Infered types are not convertible."
                | Some [] -> Eval.eq_modulo [] t u
                | Some cs ->
                    List.iter (fatal_msg "Cannot solve %a.\n" pp_constr) cs;
                    fatal q.pos "Infered types are not convertible."
              end
          | (None   , _      ) ->
              fatal pt.pos "The type of the LHS cannot be infered."
          | (_      , None   ) ->
              fatal pu.pos "The type of the RHS cannot be infered."
      in
      if result = must_fail then fatal q.pos "Assertion failed.";
      out 3 "(asrt) assertion OK\n";
  | P_query_debug(e,s)     ->
      (* Just update the option, state not modified. *)
      Console.set_debug e s;
      out 3 "(flag) debug → %s%s\n" (if e then "+" else "-") s
  | P_query_verbose(i)     ->
      (* Just update the option, state not modified. *)
      Timed.(Console.verbose := i);
      out 3 "(flag) verbose → %i\n" i
  | P_query_flag(id,b)     ->
      (* We set the value of the flag, if it exists. *)
      begin
        try Console.set_flag id b with Not_found ->
          wrn q.pos "Unknown flag \"%s\"." id
      end;
      out 3 "(flag) %s → %b\n" id b
  | P_query_infer(pt, cfg)            ->
      (* Infer the type of [t]. *)
      let t = scope pt in
      let a =
        match Typing.infer ss (Env.to_ctxt env) t with
        | Some(a) -> Eval.eval cfg [] a
        | None    -> fatal pt.pos "Cannot infer the type of [%a]." pp t
      in
      out 3 "(infr) %a : %a\n" pp t pp a
  | P_query_normalize(pt, cfg)        ->
      (* Infer a type for [t], and evaluate [t]. *)
      let t = scope pt in
      let v =
        match Typing.infer ss (Env.to_ctxt env) t with
        | Some(_) -> Eval.eval cfg [] t
        | None    -> fatal pt.pos "Cannot infer the type of [%a]." pp t
      in
      out 3 "(comp) %a\n" pp v
  | P_query_prover(s)      ->
      Timed.(Why3_tactic.default_prover := s)
  | P_query_prover_timeout(n)->
      Timed.(Why3_tactic.timeout := n)
