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
open! Lplib
open Base
open Timed

(** [infer pos p c t] returns a type for the term [t] in context [c] and under
   the constraints of [p] if there is one, or
@raise Fatal. [c] must well sorted. Note that [p] gets modified. *)
let infer : Pos.popt -> problem -> ctxt -> term -> term = fun pos p ctx t ->
  match Infer.infer_noexn p ctx t with
  | None -> fatal pos "%a is not typable." pp_term t
  | Some a ->
      if Unif.solve_noexn p then
        begin
          if !p.unsolved = [] then a
          else
            (List.iter (wrn pos "Cannot solve %a.@." pp_constr) !p.unsolved;
             fatal pos "Failed to infer the type of %a." pp_term t)
        end
      else fatal pos "%a is not typable." pp_term t

(** [check pos p c t a] checks that the term [t] has type [a] in context [c]
and under the constraints of [p], or
@raise Fatal. [c] must well sorted. Note that [p] gets modified. *)
let check : Pos.popt -> problem -> ctxt -> term -> term -> unit =
  fun pos p ctx t a ->
  if Infer.check_noexn p ctx t a then
    if Unif.solve_noexn p then
      begin
        if !p.unsolved <> [] then
          (List.iter (wrn pos "Cannot solve %a.@." pp_constr) !p.unsolved;
           fatal pos "[%a] does not have type [%a]." pp_term t pp_term a)
      end
    else fatal pos "[%a] does not have type [%a]." pp_term t pp_term a

(** [check_sort pos p c t] checks that the term [t] has type [Type] or [Kind]
   in context [c] and under the constraints of [p], or
@raise Fatal. [c] must be well sorted. *)
let check_sort : Pos.popt -> problem -> ctxt -> term -> unit =
  fun pos p ctx t ->
  match Infer.infer_noexn p ctx t with
  | None -> fatal pos "[%a] is not typable." pp_term t
  | Some a ->
      if Unif.solve_noexn p then
        begin
          if !p.unsolved = [] then
            match unfold a with
            | Type | Kind -> ()
            | _ -> fatal pos "[%a] has type [%a] and not a sort."
                     pp_term t pp_term a
          else
            (List.iter (wrn pos "Cannot solve %a.@." pp_constr) !p.unsolved;
             fatal pos "Failed to check that [%a] is typable by a sort."
               pp_term a)
        end
      else fatal pos "[%a] is not typable." pp_term t

(** Result of query displayed on hover in the editor. *)
type result = (unit -> string) option

(** [return pp x] prints [x] using [pp] on [Stdlib.(!out_fmt)] at verbose
   level 1 and returns a function for printing [x] on a string using [pp]. *)
let return : 'a pp -> 'a -> result = fun pp x ->
  Console.out 1 (Color.red "%a") pp x;
  Some (fun () -> Format.asprintf "%a" pp x)

(** [handle_query ss ps q] *)
let handle : Sig_state.t -> proof_state option -> p_query -> result =
  fun ss ps {elt;pos} ->
  match elt with
  | P_query_debug(e,s) ->
      Logger.set_debug e s;
      Console.out 1 "debug %s%s" (if e then "+" else "-") s;
      None
  | P_query_verbose(i) ->
      if Timed.(!Console.verbose) = 0 then
        (Timed.(Console.verbose := i);
         Console.out 1 "verbose %i" i)
      else
        (Console.out 1 "verbose %i" i;
         Timed.(Console.verbose := i));
      None
  | P_query_flag(id,b) ->
      (try Console.set_flag id b
       with Not_found -> fatal pos "Unknown flag %S." id);
      Console.out 1 "flag %s ≔ %b" id b;
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
        let open Timed in
        (* print its name and modifiers *)
        let pp_trunk ppf s =
          out ppf "%a%a%asymbol %a"
            pp_expo s.sym_expo pp_prop s.sym_prop
            pp_match_strat s.sym_mstrat pp_sym s
        in
        (* print its type *)
        let pp_type ppf s =
          out ppf ": %a" pp_prod (!(s.sym_type), s.sym_impl) in
        (* print its definition *)
        let pp_def ppf s =
          Option.iter (out ppf "≔ %a" pp_term) !(s.sym_def) in
        (* print its notation *)
        let pp_notation : Sign.notation option pp = fun ppf n ->
          Option.iter
            (out ppf "notation %a %a@." pp_sym s pp_notation) n in
        (* print its rules *)
        let pp_rules ppf s =
          match !(s.sym_rules) with
          | [] -> ()
          | rs -> let pp_rule ppf r = pp_rule ppf (s,r) in
                  out ppf "@[<v2>rules:@,%a@,@]" (List.pp pp_rule "@,") rs
        in
        (* print its constructors (if it is an inductive type) *)
        let pp_constructors ppf s =
          let open Sign in
          (* get the signature of [s] *)
          let sign =
            try Path.Map.find s.sym_path Timed.(!loaded)
            with Not_found -> assert false
          in
          let pp_decl : sym pp = fun ppf s ->
            out ppf "%a: %a" pp_sym s pp_term !(s.sym_type) in
          let pp_ind : ind_data pp = fun ppf ind ->
            out ppf
              "@[<v2>constructors:@,%a@]@.@[<v2>induction principle:@,%a@]"
              (List.pp pp_decl "") ind.ind_cons pp_decl ind.ind_prop
          in
          try pp_ind ppf (SymMap.find s Timed.(!(sign.sign_ind)))
          with Not_found -> ()
        in
        out ppf "@[<hov>%a@,%a@ %a@]@.%a%a%a@]"
          pp_trunk s pp_type s pp_def s pp_notation (notation_of s)
          pp_rules s pp_constructors s
      in
      return pp_sym_info (Sig_state.find_sym ~prt:true ~prv:true ss qid)
  | P_query_proofterm ->
      (match ps with
       | None -> fatal pos "Not in a proof"
       | Some ps ->
           match ps.proof_term with
           | Some m -> return pp_term (mk_Meta(m,[||]))
           | None -> fatal pos "Not in a definition")
  | _ ->
  let env = Proof.focus_env ps in
  let meta_of_key =
    match ps with
    | None -> fun _ -> None
    | Some ps -> Proof.meta_of_key ps in
  let meta_of_name =
    match ps with
    | None -> fun _ -> None
    | Some ps -> Proof.meta_of_name ps in
  let p = new_problem() in
  let scope = Scope.scope_term true ss env p meta_of_key meta_of_name in
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
      Console.out 2 "assertion: it is %b that %a" (not must_fail)
        pp_typing (ctxt, t, a);
      (* Check that [a] is typable by a sort. *)
      check_sort pos p ctxt a;
      let result =
        try check pos p ctxt t a; true
        with Fatal _ -> false
      in
      if result = must_fail then fatal pos "Assertion failed.";
      None
  | P_query_assert(must_fail, P_assert_conv(pt,pu)) ->
      let t = scope pt and u = scope pu in
      Console.out 2 "assertion: it is %b that %a" (not must_fail)
        pp_constr (ctxt, t, u);
      (* Check that [t] is typable. *)
      let a = infer pt.pos p ctxt t in
      (* Check that [u] is typable. *)
      let b = infer pu.pos p ctxt u in
      (* Check that [t] and [u] have the same type. *)
      p := {!p with to_solve = (ctxt,a,b)::!p.to_solve};
      if Unif.solve_noexn p then
        if !p.unsolved = [] then begin
          if Eval.eq_modulo ctxt t u = must_fail then
             fatal pos "Assertion failed."
        end else begin
          List.iter (wrn pos "Cannot solve [%a].@." pp_constr) !p.unsolved;
          fatal pos "[%a] has type [%a],@ [%a] has type [%a]@.\
                    Those two types are not unifiable."
            pp_term t pp_term a pp_term u pp_term b
        end else
          fatal pos "[%a] has type [%a].,@ [%a] has type [%a].@.\
                    Those two types are not unifiable."
            pp_term t pp_term a pp_term u pp_term b;
      None
  | P_query_infer(pt, cfg) ->
      return pp_term (Eval.eval cfg ctxt (infer pt.pos p ctxt (scope pt)))
  | P_query_normalize(pt, cfg) ->
      let t = scope pt in
      ignore (infer pt.pos p ctxt t);
      return pp_term (Eval.eval cfg ctxt t)
