(** Implementation of the REWRITE tactic. *)

open Terms
open Print
open Console
open Proofs

(****************************************************************************)

(* Error function. *)
let fail_to_match = fun n ->
  match n with
  | 0 -> fatal_no_pos "Can only use rewrite with equalities."
  | _ -> fatal_no_pos "Incorrect error code."

(** [get_lr] is given the type of the term passed as an argument to
    #REWRITE and checks that it is an equality type. That is, it checks that
    t matches with:
                          "P" ("eq" 'a l r)
    If it does then it returns (l, 2) otherwise it throws a fatal error. *)
let get_lr : term -> term * term = fun t ->
  match t with
  | Appl (Symb x, t1) ->
      if x.sym_name = "P" then
        match t1 with
        | Appl (Symb y, t2) -> if y.sym_name = "eq" then
                                 match t2 with
                                 |  -> fail_to_match 0
        | _                 -> fail_to_match 0
      else fail_to_match 0
  | _                 -> fail_to_match 0


(* TODO:
 *  -Execute the rewrite tactic
 *  -Look at handle_refine:
 *    -Get current theorm + Goal (same 2 lines).
 *
 *
 *
 *
 * *)

(** [handle_rewrite] is given a term which must be of the form l = r (for now
    with no quantifiers) and replaces the first instance of l in g with the
    corresponding instance of r. *)
let handle_rewrite : term -> unit = fun t ->
  (* Get current theorem, focus goal and the metavariable representing it. *)
  let thm = current_theorem() in
  let g = thm.t_focus in
  let m = g.g_meta in
  (* Check that the term passed as an argument to rewrite has the correct
   * type, i.e. represents an equaltiy. *)
  let t_type =
    match Solve.infer (Ctxt.of_env g.g_hyps) t with
    | None -> fatal_no_pos "Cannot find type."
    | Some a -> a
  in
  let (l, r) = get_lr t_type in
  wrn "Not implemented REWRITE tactic [%a]\n" pp t

