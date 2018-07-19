(** Implementation of the REWRITE tactic. *)

open Timed
open Terms
open Print
open Console
open Proofs

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

(** [break_eq] is given the type of the term passed as an argument to #REWRITE
    and checks that it is an equality type. That is, it checks that t matches
    with:
                          "P" ("eq" a l r)
    That is:
      Appl((Symb "P") , (Appl(Appl(Appl((Symb "eq") , (Symb a )) , l) , r ))
    If the argument does match a term of the shape l = r then it returns the
    triple (a, l, r) otherwise it throws a fatal error. *)
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
        | (e, [a ; l ; r]) -> check_symb e "eq" ; (a, l, r)
        | _                -> fail_to_match 0
      end
  | _ -> fail_to_match 0

(** [term_match] is given two terms (for now) and determines if they match.
    at this stage this is just done by using the syntactic equality function
    from Terms, but it will change. *)
let term_match : term -> term -> bool = fun t1 t2 -> eq t1 t2

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

(** [handle_rewrite] is given a term which must be of the form l = r (for now
    with no quantifiers) and replaces the first instance of l in g with the
    corresponding instance of r. *)
let handle_rewrite : term -> unit = fun t ->
  (* Get current theorem, focus goal and the metavariable representing it. *)
  let thm = current_theorem() in
  let (g, gs) =
    match thm.t_goals with
    | []    -> fatal_no_pos "No remaining goals..."
    | g::gs -> (g, gs)
  in
  let m = g.g_meta in
  let t_type =
    match Solve.infer (Ctxt.of_env g.g_hyps) t with
    | Some a -> a
    | None   -> fatal_no_pos "Cannot find type."
  in
  (* Check that the term passed as an argument to rewrite has the correct
   * type, i.e. represents an equaltiy and get the subterms l,r from l = r
   * as well as their type a. *)
  let (a, l, r) = break_eq t_type               in
  (* Make a new free variable X and pass it in match_subst. Using bindlib and
   * pred make a new term prod, which is Pi X. G[X], where G is the type of the
   * current goal and G[X] is the result of match_subst l. *)
  let x         = Bindlib.new_var mkfree "X"    in
  let pred      = lift (match_subst g.g_type l (Vari x))  in
  let bind_p    = Bindlib.unbox (Bindlib.bind_var x pred) in
  let prod      = Prod (a, bind_p)         in
  (* Construct the type of the new goal, which is G[r] and build the meta
   * of the new goal by using the information from the old meta and the new
   * type constructed above. *)
  let new_type  = Bindlib.subst bind_p r   in
  let meta_env  = Array.map Bindlib.unbox (Env.vars_of_env g.g_hyps)   in
  let new_m     = fresh_meta new_type (m.meta_arity) in
  let new_meta  = Meta(new_m, meta_env) in
  (* Get the inductive assumption of Leibniz equality to transform a proof of
   * the new goal to a proof of the previous goal. *)
  (* FIXME: When a Logic module with a notion of equality is defined get this
   * from that module. *)
  let eq_ind    = Symb(Sign.find (Sign.current_sign()) "eqind")        in
  (* Build the term tht will be used in the instantiation of the new meta. *)
  let g_m       = add_args eq_ind [a ; l ; r ; t ; prod ; new_meta]    in
  let b = Bindlib.bind_mvar (to_tvars meta_env) (lift g_m) in
  let b = Bindlib.unbox b in
  (*
   * FIXME: Type check the term used to instantiate the old meta.
   * if not (Solve.check (Ctxt.of_env g.g_hyps) g_m !(m.meta_type)) then
   * fatal_no_pos "Typing error.";
  *)
  m.meta_value := Some b ;
  let thm = {thm with t_goals = {g with g_meta = new_m ; g_type = new_type }::gs} in
  theorem := Some thm ;
  begin
    wrn "Goal : [%a]\n" pp g.g_type ;
    wrn "Lemma: [%a]\n" pp t        ;
    wrn "Left : [%a]\n" pp l        ;
    wrn "Right: [%a]\n" pp r        ;
    wrn "Prod:  [%a]\n" pp prod     ;
    wrn "New T: [%a]\n" pp new_type ;
    wrn "New:   [%a]\n" pp g_m      ;
  end

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
