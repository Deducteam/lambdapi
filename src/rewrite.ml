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

(** A substitution is a mapping from metavariables to terms. *)
type substitution = (term * term) list

(** [make_meta env] builds a fresh metavariable given the environment [env]. A
    call to this function does exactly corresponds to the scoping of wildcards
    when every variable of [env] is in scope (see [Scope.scope_term], [P_Wild]
    case. *)
let make_meta : Env.t -> term = fun env ->
  let vs = Env.vars_of_env env in
  let a =
    let m = fresh_meta (Env.prod_of_env env _Type) (Array.length vs) in
    Env.prod_of_env env (_Meta m vs)
  in
  Bindlib.unbox (_Meta (fresh_meta a (List.length env)) vs)

(** [break_prod] is given the equality proof and its type and it replaces
    with fresh metas from make_meta all the quantified variables in t_type.
    At the same time it applies the new metavariables tot the equality proof,
    so that afterwards they are substituted with the right terms. *)
let break_prod : term -> term -> Env.t -> term * term = fun t t_type env ->
  let rec break_prod_aux : term -> term -> term * term = fun t t_type ->
    match t_type with
    | Prod(_,b) ->
        let m = make_meta env in
        let b = Bindlib.subst b m in
        break_prod_aux (Appl(t,m)) b
    | _ -> (t, t_type)
  in
  break_prod_aux t t_type

(** [apply_sub t sub] applies the substitution [sub] to the term [t].  It goes
    through the term [t],  replacing the metavariables of the term with values
    provided in the substitution (if any). *)
let apply_sub : term -> substitution -> term = fun t sub ->
  let rec apply_sub_aux : term -> term = fun t ->
    let t = unfold t in
    match t with
    | Meta(_)     ->
        let p = try Some (List.assoc t sub) with Not_found -> None in
      begin
         match p with
          | Some p -> p
          | None   -> t
      end
    | Appl(t1,t2) -> Appl(apply_sub_aux t1, apply_sub_aux t2)
    | _           -> t
  in
  apply_sub_aux t

(** [build_sub] is given two terms, with the second one potentially containing
    metavariables, and tries to finds the substitution unifying them. *)
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
          let p = try Some (List.assoc l acc) with Not_found -> None in
          match p with
          | Some _ -> Some acc
          | None   -> Some ((l,t)::acc)
        end
    | (_, _)                 -> None
  in build_sub_aux g l []

(** [find_sub] is given two terms and finds the first instance of  the  second
    term in the first, if one exists, and returns the substitution giving rise
    to this instance or an empty substitution otherwise. *)
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

(** [bind_match t1 t2] produces a binder that abstracts away all the occurence
    of the term [t1] in the term [t2].  We require that [t2] does not  contain
    products, abstraction, metavariables, or other awkward terms. *)
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
  (* Obtain the required symbols from the current signature. *)
  (* FIXME use a parametric notion of equality. *)
  let sign = Sign.current_sign () in
  let find_sym : string -> sym = fun name ->
    try Sign.find sign name with Not_found ->
    fatal_no_pos "Current signature does not define symbol [%s]." name
  in
  let sign_P  = find_sym "P"  in
  let sign_T  = find_sym "T"  in
  let sign_eq = find_sym "eq" in
  let sign_eqind = find_sym "eqind" in

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

  (* Check that the type of [t] is of the form “P (Eq a l r)”. *)
  let (t, t_type) = break_prod t t_type g.g_hyps in
  let (a, l, r)  =
    match get_args t_type with
    | (p,[eq]) when is_symb sign_P p ->
        begin
          match get_args eq with
          | (e,[a;l;r]) when is_symb sign_eq e -> (a, l, r)
          | _                                  ->
              fatal_no_pos "Rewrite expected equality type (found [%a])." pp t
        end
    | _                              ->
        fatal_no_pos "Rewrite expected equality type (found [%a])." pp t
  in

  (* Extract the term from the goal type (get “t” from “P t”). *)
  let g_term =
    match get_args g.g_type with
    | (p, [t]) when is_symb sign_P p -> t
    | _                              ->
        fatal_no_pos "Rewrite expects a goal of the form “P t” (found [%a])."
          pp g.g_type
  in

  let sigma = find_sub g_term l in
  let (l,r) = (apply_sub l sigma, apply_sub r sigma) in
  let t = apply_sub t sigma in
  let pred_bind = bind_match l g_term in
  let pred = Abst(Appl(Symb(sign_T), a), pred_bind) in

  (* Construct the new goal and its type. *)
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
