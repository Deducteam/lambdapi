(** Implementation of the REWRITE tactic. *)

open Terms
open Print
open Console
open Proofs

(****************************************************************************)

(* Trying things out. *)
let rec find_term = fun t ->
  match t with
  | Vari _           -> print_string "Vari "
  | Type             -> print_string "Type "
  | Kind             -> print_string "Kind "
  | Symb x           -> print_string "Symb - " ; print_string x.sym_name ;
                        print_string " "
  | Prod _           -> print_string "Prod "
  | Abst _           -> print_string "Abst "
  | Appl (t1, t2)    -> print_string "Appl of [" ; find_term t1  ;
                        print_string "] to ["     ; find_term t2 ;
                        print_string "]"
  | Meta _           -> print_string "Meta "
  | _                -> print_string "Suuuuure"


(* Error function. *)
let fail_to_match = fun n ->
  match n with
  | 0 -> fatal_no_pos "Can only use rewrite with equalities."
  | _ -> fatal_no_pos "Incorrect error code."

(* Minimal unwrapper. *)
let get : 'a option -> 'a = fun t ->
  match t with
  | Some x -> x
  | None   -> fail_to_match 0

(** [get_lr] is given the type of the term passed as an argument to
    #REWRITE and checks that it is an equality type. That is, it checks that
    t matches with:
                          "P" ("eq" 'a l r)
    That is:
      Appl((Symb "P") , (Appl(Appl(Appl((Symb "eq") , (Symb 'a )) , l) , r ))
    If it does then it returns (l, r) otherwise it throws a fatal error. *)
let get_lr : term -> term * term = fun t ->
  let check_symb : term -> string -> term option = fun t name ->
    match t with
    | Appl(Symb x, t1) -> if x.sym_name = name then Some t1 else None
    | _                -> None
  in
  let subterm : term -> (term * term) option = fun t ->
    match t with
    | Appl(t1, sub) -> Some (t1, sub)
    | _             -> None
  in
  let t1      = get (check_symb t "P"  ) in
  let (t2, r) = get (subterm t1        ) in
  let (t3, l) = get (subterm t2        ) in
  let _       = get (check_symb t3 "eq") in (l,r)

(****************************************************************************)
(* TODO:
 *  -Execute the rewrite tactic
 *  -Look at handle_refine:
 *    -Get current theorm + Goal (same 2 lines). *)
(****************************************************************************)

(** [handle_rewrite] is given a term which must be of the form l = r (for now
    with no quantifiers) and replaces the first instance of l in g with the
    corresponding instance of r. *)
let handle_rewrite : term -> unit = fun t ->
  (* Get current theorem, focus goal and the metavariable representing it. *)
  let thm = current_theorem() in
  let g =
    match thm.t_goals with
    | []   -> fatal_no_pos "No remaining goals..."
    | g::_ -> g
  in
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
(* So we check that the thing given to rewrite is of the right form, i.e.
 * an equality. Then what?
 * *)

(* ------------ 1 ----------
 * Around here we need to find the occurrences of the first instance of l in m
 * or somewhere, this is still unclear to me.
 * - Note that there is a syntactic equality checker somewhere (it's a hack)
 *)

(* ------------ 2 ----------
 * Next these occurrences need to be substituted by r.
 *)

(* ------------ 3 ----------
 * Then using the definition of eq the type of the new goal
 *              - what new goal rn? -
 * needs to be mapped to the old goal, right? *)

