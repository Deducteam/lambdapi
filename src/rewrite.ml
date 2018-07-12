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

(****************************************************************************)

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

(****************************************************************************)

(** [get_lr] is given the type of the term passed as an argument to
    #REWRITE and checks that it is an equality type. That is, it checks that
    t matches with:
                          "P" ("eq" 'a l r)
    That is:
      Appl((Symb "P") , (Appl(Appl(Appl((Symb "eq") , (Symb 'a )) , l) , r ))
    If the argument does match a term of the shape l = r then it returns (l, r)
    otherwise it throws a fatal error. *)
let get_lr : term -> term * term = fun t ->
  let check_symb : term -> string -> term option = fun t name ->
    match unfold t with
    | Appl(Symb x, t1) -> if x.sym_name = name then Some t1 else None
    | _                -> None
  in
  let subterm : term -> (term * term) option = fun t ->
    match unfold t with
    | Appl(t1, sub) -> Some (t1, sub)
    | _             -> None
  in
  let t1      = get (check_symb t "P"  ) in
  let (t2, r) = get (subterm t1        ) in
  let (t3, l) = get (subterm t2        ) in
  let _       = get (check_symb t3 "eq") in (l,r)

(** [term_match] is given two terms (for now) and determines if they match.
    at this stage this is just done by using the syntactic equality function
    from Terms, but it will change. *)
let rec term_match : term -> term -> bool = fun t1 t2 -> eq t1 t2

(** [instances] is a helper function that given two terms t and s returns
    all occurrences of s in t.
    It will not be in the final code, as for now it tests syntactic equality
    as we expect that the term l (in l = r) is ground. This is just to see if
    things work. *)
let instances : term -> term -> term list = fun t s ->
  let rec instances_aux : term -> term list -> term list = fun cur acc ->
      match unfold cur with
      | Vari x       -> if term_match cur s then cur::acc else acc
      | Type | Kind  -> acc
      | Symb sym     -> if term_match cur s then cur::acc else acc
      | Prod(t1, _) | Abst(t1, _)
                     -> instances_aux t1 acc (* Not sure how to use the
                                              * function Terms.get_args. *)
      | Appl(t1, t2) ->
        let rest = instances_aux t2 (instances_aux t1 acc) in
        if term_match cur s then cur :: rest else rest
      | Meta _       ->  if term_match cur s then cur::acc else acc
      | _            -> acc
    in instances_aux t []


(****************************************************************************)
(* TODO:
 *  -Execute the rewrite tactic
 *  -Look at handle_refine
 *
 *
 *
 *
 *)
(****************************************************************************)

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
    | Some a -> a
    | None   -> fatal_no_pos "Cannot find type."
  in
  let (l, r) = get_lr t_type in
  let sub = instances g.g_type l in
  begin
    wrn "Goal : [%a]\n" pp g.g_type ;
    wrn "Lemma: [%a]\n" pp t        ;
    wrn "Left : [%a]\n" pp l        ;
    wrn "Right: [%a]\n" pp r
  end
(* So we check that the thing given to rewrite is of the right form, i.e.
 * an equality. Then what?
 * *)

(* ------------ TODO 1 ----------
 * Around here we need to find the occurrences of the first instance of l in m
 * or somewhere, this is still unclear to me.
 * - Note that there is a syntactic equality checker somewhere (it's a hack)
 * TODO - Try more tests, when people come around.
 *      - Add the function to a "substitutor"
 *)

(* ------------ TODO 2 ----------
 * Next these occurrences need to be substituted by r.
 * - Initially just syntactically on the type of g' (i.e. the new goal).
 *)

(* ------------ TODO 3 ----------
 * * Then using the definition of eq the type of the new goal
 *              - what new goal rn? -
 * needs to be mapped to the old goal, right? *)

