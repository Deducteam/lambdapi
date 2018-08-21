(** Implementation of the REWRITE tactic. *)

open Timed
open Terms
open Print
open Console
open Proofs
open Solve

(** Logging function for the rewrite tactic. *)
let log_rewr = new_logger 'w' "rewr" "informations for the rewrite tactic"
let log_rewr = log_rewr.logger

type substitution = (term * term) list

(****************************************************************************)
(* Obtain the required symbols from the current signature. *)
(* FIXME use a parametric noton of equality. *)
let find_sym : string -> Sign.t -> sym = fun name sign ->
    try Sign.find sign name with Not_found ->
    fatal_no_pos "Current signature does not define symbol [%s]." name

let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with
  | Symb(r) -> r == s
  | _       -> false
(*****************************************************************************)
(** [break_prod] is given the type of the term passed to #REWRITE which is
    assumed to be of the form
                    !x1 : A1 ... ! xn : An U
    and it returns (n, U). *)
(* TODO integrate this with the rest of the code. *)
let break_prod : term -> int * term = fun t ->
   let rec break_prod_aux t acc =
     match t with
     | Prod(a,b) -> let (v,b) = Bindlib.unbind b in break_prod_aux b (1+acc)
     | _ -> (acc, t)
   in break_prod_aux t 0

(** [break_eq] is given the type of the term passed as an argument to #REWRITE
    and checks that it is an equality proof. That is, it checks that t matches
    with:
                          "P" ("eq" a l r)
    If the argument does match a term of the shape l = r then it returns the
    triple (a, l, r) otherwise it throws a fatal error. *)
let break_eq : Sign.t ->term -> term * term * term = fun sign t ->
    match get_args t with
    | (p,[eq]) when is_symb (find_sym "P" sign) p ->
        begin
          match get_args eq with
          | (e,[a;l;r]) when is_symb (find_sym "eq" sign) e -> (a, l, r)
          | _                                  ->
              fatal_no_pos "Rewrite expected equality type (found [%a])." pp t
        end
    | _                              ->
        fatal_no_pos "Rewrite expected equality type (found [%a])." pp t
(*****************************************************************************)

(** [apply_sub] is given a term and a substitution and returns the  result  of
    applying the substitution to the term. *)
let apply_sub : term -> substitution -> term = fun t sub ->
  let rec apply_sub_aux : term -> term = fun t ->
    let t = unfold t in
    match t with
    | Meta(_)     -> let p = List.assoc_opt t sub in
      begin
         match p with
          | Some p -> p
          | None   -> t
      end
    | Appl(t1,t2) -> Appl(apply_sub_aux t1, apply_sub_aux t2)
    | _           -> t
  in
  apply_sub_aux t

(** [build_sub] is given a two terms and finds the substitution  that  unifies
    them, if one exist. *)
let build_sub : term -> term -> substitution option = fun g l ->
  let rec build_sub_aux :
    term -> term -> substitution -> substitution option = fun g l acc ->
    match (g,l) with
    | (Type, Type)           -> Some acc
    | (Kind, Kind)           -> Some acc
    | (Symb(x), Symb(y))     -> if x==y then Some acc else None
    | (Appl(x1,y1), Appl(x2,y2)) ->
        begin
          match build_sub_aux x1 x2 acc with
          | Some subst -> build_sub_aux y1 y2 subst
          | None       -> None
        end
    | (t, Meta(_))           ->
        begin
          let  p = List.assoc_opt t acc in
          match p with
          | Some _ -> Some acc
          | None   -> Some ((l,t)::acc)
        end
    | (_, _)                 -> None
  in build_sub_aux g l []

(** [apply_sub] is given a two terms, finds the first instance of  the  second
    term in the first, if one exists and returns the substitution giving  rise
    to this instance or None otherwise. *)
let find_sub : term -> term -> substitution = fun g l ->
  let rec find_sub_aux : term -> substitution option = fun g ->
    match build_sub g l with
    | Some sub -> Some sub
    | None     ->
      begin
          match g with
          | Appl(x,y) ->
             begin
              match find_sub_aux x with
              | Some sub -> Some sub
              | None     -> find_sub_aux y
             end
          | _ -> None
      end
  in
  match find_sub_aux g with
  | Some sub -> sub
  | None -> []

(** [bind_match t1 t2] binds every occurence of the term [t1] in the term [t2].
    Note that [t2] should not contain products, abstractions, metavariables, or
    other awkward terms. *)
let bind_match : term -> term -> (term, term) Bindlib.binder = fun t1 t2 ->
  let x = Bindlib.new_var mkfree "X" in
  (* NOTE we lift to the bindbox while matching (for efficiency). *)
  let rec lift_subst : term -> tbox = fun t ->
    if Terms.eq t1 t then _Vari x else
    match unfold t with
    | Vari(y)     -> _Vari y
    | Type        -> _Type
    | Kind        -> _Kind
    | Symb(s)     -> _Symb s
    | Appl(t,u)   -> _Appl (lift_subst t) (lift_subst u)
    (* For now, we fail on products, abstractions and metavariables. *)
    | Prod(_)     -> fatal_no_pos "Cannot rewrite under products."
    | Abst(_)     -> fatal_no_pos "Cannot rewrite under abstractions."
    | Meta(_)     -> fatal_no_pos "Cannot rewrite metavariables."
    (* Forbidden cases. *)
    | Patt(_,_,_) -> assert false
    | TEnv(_,_)   -> assert false
  in
  Bindlib.unbox (Bindlib.bind_var x (lift_subst t2))

(** [handle_rewrite t] rewrites according to the equality proved by [t] in the
    current goal. The term [t] should have a type corresponding to an equality
    (without any quantifier for now). All instances of the LHS are replaced by
    the RHS in the obtained goal. *)
let handle_rewrite : term -> unit = fun t ->
  let sign = Sign.current_sign () in
  let sign_P = find_sym "P" sign in
  let sign_T = find_sym "T" sign  in
  let sign_eqind = find_sym "eqind" sign in
  (* Get the focused goal, and related data. *)
  let thm = current_theorem () in
  let (g, gs) =
    match thm.t_goals with
    | []    -> fatal_no_pos "No remaining goals..."
    | g::gs -> (g, gs)
  in

  (* Infer the type of [t] (the argument given to the tactic). *)
  let g_ctxt = Ctxt.of_env g.g_hyps in
  let t_type =
    match Solve.infer g_ctxt t with
    | Some(a) -> a
    | None    ->
        fatal_no_pos "Cannot infer the type of [%a] (given to rewrite)." pp t
  in
  (* Check that the type of [t] is of the form “P (Eq a l r)”. and return the
   * parameters. *)
  let (n, t_type) = break_prod t_type in
  let (a, l, r)   =  break_eq sign t_type in
  (* Extract the term from the goal type (get “t” from “P t”). *)
  let g_term =
    match get_args g.g_type with
    | (p, [t]) when is_symb sign_P p -> t
    | _                              ->
        fatal_no_pos "Rewrite expects a goal of the form “P t” (found [%a])."
          pp g.g_type
  in
  (***************************************************************************)
  let sigma = find_sub g_term l in
  let (l,r) = (apply_sub l sigma, apply_sub r sigma) in
  let t = apply_sub t sigma in
  (***************************************************************************)
  (* Build the predicate by matching [l] in [g_term]. *)
  (* TODO keep track of substitutions in the first instance of l in g. *)
  let pred_bind = bind_match l g_term in
  let pred = Abst(Appl(Symb(sign_T), a), pred_bind) in

  (* Construct new goal and it type. *)
  let goal_type = Appl(Symb(sign_P), Bindlib.subst pred_bind r) in
  let goal_term = Ctxt.make_meta g_ctxt goal_type in
  let new_goal =
    match goal_term with
    | Meta(m,_) -> m
    | _         -> assert false (* Cannot happen. *)
  in

  (* Build the final term produced by the tactic, and check its type. *)
  let term = add_args (Symb(sign_eqind)) [a; l; r; t; pred; goal_term] in
  if not (Solve.check g_ctxt term g.g_type) then
    begin
      match Solve.infer g_ctxt term with
      | Some(a) ->
          fatal_no_pos "The term produced by rewrite has type [%a], not [%a]."
            pp (Eval.snf a) pp g.g_type
      | None    ->
          fatal_no_pos "The term [%a] produced by rewrite is not typable."
            pp term
    end;

  (* Instantiate the current goal. *)
  let meta_env = Array.map Bindlib.unbox (Env.vars_of_env g.g_hyps)  in
  let b = Bindlib.bind_mvar (to_tvars meta_env) (lift term) in
  g.g_meta.meta_value := Some(Bindlib.unbox b);

  (* Update current theorem with the newly created goal. *)
  let new_g = {g_meta = new_goal; g_hyps = g.g_hyps; g_type = goal_type} in
  theorem := Some({thm with t_goals = new_g :: gs});

  log_rewr "Rewriting with:";
  log_rewr "  goal           = [%a]" pp g.g_type;
  log_rewr "  equality proof = [%a]" pp t;
  log_rewr "  equality type  = [%a]" pp t_type;
  log_rewr "  equality LHS   = [%a]" pp l;
  log_rewr "  equality RHS   = [%a]" pp r;
  log_rewr "  pred           = [%a]" pp pred;
  log_rewr "  new goal       = [%a]" pp goal_type;
  log_rewr "  produced term  = [%a]" pp term

(* --------------- TODO (From the meetings on 26/07/2018) ------------------ *)
(*****************************************************************************
 * 1) Rewrite in hypotheses. (Sept.) *** - 2 weeks?
 *    This would be the implementation of a similar tactic called #REWRITE_IN
 *    which given a hypothesis an an equality proof rewrites in the hypothesis.
 *    The core mechanism should be the same, but what is updated in the end
 *    woud change. Difficulties
 *      a) Change the parser to handle the new command.
 *      b) Find out what happens when a hypothesis is rewritten.
 * 2) Basic patterns. (Jul. - Sept.) ****
 *    The lemma passed to rewrite is allowed to have quantifiers, so it is of
 *    the form:
 *        !x1:T1 ... !xn:Tn.  l(x1, ..., xn) = r(x1, ..., xn).
 *    Then we need to find the first instance of l in g_type, keep the substi-
 *    tution and rewrite all such instances with the corresponding instances of
 *    r.
 * 3) Full SSReflect patterns. (Spet.) ****
 *    This would mainly involve nesting the machinery from 4 but it is not that
 *    simple.
 *)
