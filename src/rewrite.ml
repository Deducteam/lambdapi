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

(** [break_prod] is a less safe version of Handle.env_of_prod. It is given the
    type of the term passed to #REWRITE which is assumed to be of the form
                    !x1 : A1 ... ! xn : An U
    and it returns an environment [x1 : A1, ... xn : An] and U. *)
(* TODO: Replace this by Handle.env_of_prod if it is possible to get the
 * number of products in a term. *)
let break_prod : term -> Env.t * term = fun t ->
   let rec aux t acc =
     match t with
     | Prod(a,b) ->
        let (v,b) = Bindlib.unbind b in
        aux b ((Bindlib.name_of v,(v,lift a))::acc)
     | _ -> acc, t
   in aux t []

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
    let cur = unfold cur in
    if term_match cur l then t else match cur with
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
  let g_meta = g.g_meta in
  let g_ctxt = Ctxt.of_env g.g_hyps in
  let t_type =
    match Solve.infer g_ctxt t with
    | Some a -> a
    | None   -> fatal_no_pos "Cannot infer type of argument passed to rewrite."
  in
  (* Check that the term passed as an argument to rewrite has the correct
   * type, i.e. represents an equaltiy and get the subterms l,r from l = r
   * as well as their type a. *)
  (*************************************************************************)
  (* TODO: Basic patterns. This should start with something like:
   *       let (env, t_type)  = break_prod t_type in
   * and keep track of substitutions in the first instance of l in g. *)
  (*************************************************************************)
  let (a, l, r) = break_eq t_type     in

  (*************************************************************************)
  (* TODO: Remove this. We keep it for now to print types, for debugging. *)
  let l_type =
    match Solve.infer g_ctxt l with
    | Some a -> a
    | None   -> fatal_no_pos "Cannot infer type of LHS."
  in
  (*************************************************************************)

  (* Make a new free variable X and pass it in match_subst to take the place of
   * the RHS of the equality proof. *)
  let x = Bindlib.new_var mkfree "X"  in
  (* g_subst is the term obtained by replacing the occurrences of l in g with
   * the new free variable X. *)
  let g_subst = (match_subst g.g_type l (Vari x)) in
  (* We know that g_subst is of the form App("P", T ), and we want to build a
   * term of the form App("P", Abst(X, T)) so we break it up and then build it
   * again, correctly. *)
  let (p_symb, t1, ts)  =
    match  get_args g_subst with
    |(_, [])     -> fatal_no_pos "Should not get here."
    |(p, t1::ts) -> (p, t1, ts)
  in
  let g_subst   = add_args t1 ts     in
  (* We build the predicate
   *              X : T a => g_subst[X]
   * this is later passed as an argument to eq_ind. *)
  let pred_bind   = lift g_subst     in
  let pred_bind   = Bindlib.unbox (Bindlib.bind_var x pred_bind)    in
  (* FIXME: Get encodings from some standard signature, when it is defined. *)
  let t_symb  = Symb(Sign.find (Sign.current_sign()) "T")           in
  let t_a     = Appl(t_symb, a)      in
  let pred    = Abst(t_a, pred_bind) in

  (*************************************************************************)
  (* TODO: Remove this. We keep it for now to print types, for debugging. *)
  let pred_type =
    match Solve.infer g_ctxt pred with
    | Some a -> a
    | None   -> fatal_no_pos "Cannot infer type of pred."
  in
  (*************************************************************************)

  (* Construct the type of the new goal, which is obtained by performing the
   *  subsitution by r, and adding the P symbol on top *)
  (* FIXME: There is some duplication here, that could be avoided, by perhaps
   * using Eval.snf or some other standard function. *)
  let new_type = Bindlib.subst pred_bind r   in
  let new_type = Appl(p_symb, new_type)      in

  (*************************************************************************)
  (* TODO: Remove this. We keep it for now to print types, for debugging. *)
  let new_type_type =
    match Solve.infer g_ctxt new_type with
    | Some a -> a
    | None   -> fatal_no_pos "Cannot infer type of the new type."
  in
  (*************************************************************************)

  (* Build the new meta variable. As a term it will be used in eq_ind later on
   * and as a meta it will be used to update the goal, once the rewrite tactic
   * has finished. *)
  let new_meta = Ctxt.make_meta g_ctxt new_type  in
  let new_m = match new_meta with
    | Meta(x ,_) -> x
    | _          -> fatal_no_pos "Should not get here."
  in
  (* Get the inductive principle associated with Leibniz equality to transform
   * a proof of the new goal to a proof of the previous goal. *)

  (* FIXME: When a Logic module with a notion of equality is defined get this
  from that module. *)
  let eq_ind        = Symb(Sign.find (Sign.current_sign()) "eqind")     in
  (* Build the final lambda term that the tactic has produced. *)
  let term_produced = add_args eq_ind [a ; l ; r ; t ; pred ; new_meta]  in

  (*************************************************************************)
  (* TODO: Remove this. We keep it for now to print types, for debugging. *)
  let term_produced_type =
    match Solve.infer g_ctxt term_produced with
    | Some a -> Eval.snf a
    | None   -> fatal_no_pos "Cannot infer type of the term produced."
  in
  (*************************************************************************)

  (* Type check the term used to instantiate the old meta. *)
  if not (Solve.check g_ctxt term_produced g.g_type) then
    fatal_no_pos "Fatal error : The term the rewrite tactic has produced doesn't have the expected type.";
  (* Update the value of the meta of the current goal. *)
  let meta_env = Array.map Bindlib.unbox (Env.vars_of_env g.g_hyps)  in
  let b = Bindlib.bind_mvar (to_tvars meta_env) (lift term_produced) in
  let b = Bindlib.unbox b in
  g_meta.meta_value := Some b ;
  (* "Instantiation". We don't really instantiate the new meta of the goal,
   * since #REWRITE does not change g_hyps etc. we just update the necessary
   * parameters. *)
  let thm =
    {thm with t_goals = {g with g_meta = new_m ; g_type = new_type}::gs} in
  theorem := Some thm ;

  begin
    print_endline " ------------------- Information ----------------------- " ;
    wrn "Goal:                          [%a]\n" pp g.g_type ;
    wrn "Equality proof used:           [%a]\n" pp t ;
    wrn "Type of equality proof:        [%a]\n" pp t_type ;
    wrn "LHS of the rewrite hypothesis: [%a]\n" pp l ;
    wrn "Type of the LHS:               [%a]\n" pp l_type ;
    wrn "RHS of the rewrite hypothesis: [%a]\n" pp r ;
    wrn "Pred:                          [%a]\n" pp pred ;
    wrn "Type of pred:                  [%a]\n" pp pred_type ;
    wrn "New type to prove:             [%a]\n" pp new_type ;
    wrn "Type of new type to prove:     [%a]\n" pp new_type_type ;
    wrn "Term produced:                 [%a]\n" pp term_produced ;
    wrn "Type of the term produced:     [%a]\n" pp term_produced_type ;
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
