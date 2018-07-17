(** Implementation of the REWRITE tactic. *)

open Terms
open Print
open Console
open Proofs

(****************************************************************************)

(** [find_term] just expands the AST of a given term in a very trivial way. It
    is only here for me to try some stuff out. *)

(* TODO: Remove this when testing syntax stuff is finished. *)
let rec find_term = fun t ->
  match t with
  | Vari _           -> print_string "Vari "
  | Type             -> print_string "Type "
  | Kind             -> print_string "Kind "
  | Symb x           -> print_string "Symb - " ; print_string x.sym_name ;
                        print_string " "
  | Prod _           -> print_string "Prod "
  | Abst _           -> print_string "Abst "
  | Appl (t1, t2)    -> print_string "Appl of [" ; find_term t1 ;
                        print_string "] to ["    ; find_term t2 ;
                        print_string "]"
  | Meta _           -> print_string "Meta "
  | _                -> print_string "Something went wrong!"

(****************************************************************************)

(* Error function. *)
let fail_to_match = fun n ->
  match n with
  | 0 -> fatal_no_pos "Can only use rewrite with equalities."
  | 1 -> fatal_no_pos "Cannot rewrite under products."
  | 2 -> fatal_no_pos "Cannot rewrite under abstractions."
  | 3 -> fatal_no_pos "Cannot rewrite  meta variables."
  | 4 -> fatal_no_pos "Should not get here, match_subst."
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

(* TODO: Use Terms.get_args. *)
let get_lr : term -> term * term = fun t ->
  let check_symb : term -> string -> term option = fun t name ->
    match unfold t with
    | Appl(x, t1) ->
      begin match unfold x with
      | Symb x -> if x.sym_name = name then Some t1 else None
      | _      -> None end
    | _           -> None
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


let break_eq : term -> term * term * term = fun t ->
  let check_symb : term -> string -> unit = fun t n ->
    match unfold t with
    | Symb s when s.sym_name = n -> ()
    | _ -> fail_to_match 0
  in
  match get_args t with
  | (p, [eq]) ->
      begin
        check_symb p "P" ;
        match get_args eq with
        | (e, [a ; t ; u]) -> check_symb e "eq" ; (a, t, u)
        | _ -> fail_to_match 0
      end
  | _ -> fail_to_match 0

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
                     -> instances_aux t1 acc
      | Appl(t1, t2) ->
        let rest = instances_aux t2 (instances_aux t1 acc) in
        if term_match cur s then cur :: rest else rest
      | Meta _       ->  if term_match cur s then cur::acc else acc
      | _            -> acc
    in instances_aux t []

(** [match_subst] is given the type of the current goal, the left hand side of
    the lemma rewrite was called on and some term it returns the type of the
    new goal, where all occurrences of left are replaced by the new term.
    Use: This will be called with a fresh Vari term to build a product term,
    using the bindlib lilfting functions. *)
let match_subst : term -> term -> term -> term = fun g_type l t ->
  let rec matching_aux : term -> term = fun cur ->
    if term_match (unfold cur) l then t else match unfold cur with
    | Vari _ | Type | Kind | Symb _ -> cur
    | Appl(t1, t2) ->
        let t1' = matching_aux t1 and t2' = matching_aux t2 in Appl(t1', t2')
    | Prod _  -> fail_to_match 1     (* For now we do not "mess" with any  *)
    | Abst _  -> fail_to_match 2     (* terms conaining Prodi, Abst, Meta. *)
    | Meta _  -> fail_to_match 3
    | _       -> fail_to_match 4
  in matching_aux g_type

(****************************************************************************)
(* TODO:
 *  -Execute the rewrite tactic.
 *  -Look at handle_refine.
 *  -End of document...
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
  let (a, l, r) = break_eq t_type in
  let x = Bindlib.new_var mkfree "X" in
  let pred = lift (match_subst g.g_type l (Vari x))  in
  let bind_p = Bindlib.unbox (Bindlib.bind_var x pred) in
  let prod = Prod (a, bind_p) in
  let g_type = Bindlib.subst bind_p r in
  begin
    wrn "Goal : [%a]\n" pp g.g_type ;
    wrn "Lemma: [%a]\n" pp t        ;
    wrn "Left : [%a]\n" pp l        ;
    wrn "Right: [%a]\n" pp r        ;
    wrn "New:   [%a]\n" pp prod     ;
    wrn "New:   [%a]\n" pp g_type   ;
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
 * Then using the definition of eq the type of the new goal
 *              - what new goal rn? -
 * needs to be mapped to the old goal, right? *)


(* --------------- TODO (From the meetings on 16/07/2018) ------------------ *)
(*****************************************************************************
 *  1) Take G build G[x].
 *               --> Started doing that in match_subst.
 *  2) Make a new variable X
 *  3) Compute G[X], this is simply the application of match_subst with X as
 *     the term to substitute in.
 *  4) Build Prod(X, G[X]) using bindlib.
 *****************************************************************************
 * Once the above is done we will be close to finishing the simple rewrite
 * tactic, by using:
 *      eqind T l r (lemma) (Pi X. G[X]) G'
 * or something along these lines, but we will see.
 *)
