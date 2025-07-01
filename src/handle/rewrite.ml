(** Implementation of the rewrite tactic. *)

open Lplib
open Common open Pos open Error open Debug
open Core open Term open Print
open Proof

(** Logging function for the rewrite tactic. *)
let log = Logger.make 'r' "rewr" "the rewrite tactic"
let log = log.pp

(** Equality configuration. *)
type eq_config =
  { symb_P     : sym (** Encoding of propositions.        *)
  ; symb_T     : sym (** Encoding of types.               *)
  ; symb_eq    : sym (** Equality proposition.            *)
  ; symb_eqind : sym (** Induction principle on equality. *)
  ; symb_refl  : sym (** Reflexivity of equality.         *) }

(** [get_eq_config ss pos] returns the current configuration for
    equality, used by tactics such as “rewrite” or “reflexivity”. *)
let get_eq_config : Sig_state.t -> popt -> eq_config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_P     = builtin "P"
  ; symb_T     = builtin "T"
  ; symb_eq    = builtin "eq"
  ; symb_eqind = builtin "eqind"
  ; symb_refl  = builtin "refl" }

(* Register checks for the builtin symbols related to rewriting. *)
let _ =
  let check_codomain_is_Type _ss pos sym =
    let valid =
      match Eval.whnf [] Timed.(!(sym.sym_type)) with
      | Prod(_, b) -> Eval.eq_modulo [] (snd (unbind b)) mk_Type
      | _          -> false
    in
    if not valid then
      fatal pos "The type of [%s] is not of the form [_ → TYPE]." sym.sym_name
  in
  (* The type of the builtin ["T"] should be [U → TYPE]. *)
  Builtin.register "T" check_codomain_is_Type;
  (* The type of the builtin ["P"] should be [Prop → TYPE]. *)
  Builtin.register "P" check_codomain_is_Type;
  let get_domain_of_type s =
    match Eval.whnf [] Timed.(!(s.sym_type)) with
    | Prod(a,_) -> a
    | _         -> assert false
  in
  let register_builtin =
    Builtin.register_expected_type (Eval.eq_modulo []) term
  in
  let expected_eq_type pos map =
    (* [Π (a:U), T a → T a → Prop] *)
    let symb_T = Builtin.get pos map "T" in
    let symb_P = Builtin.get pos map "P" in
    let term_U = get_domain_of_type symb_T in
    let term_Prop = get_domain_of_type symb_P in
    let a = new_var "a" in
    let term_T_a = mk_Appl (mk_Symb symb_T, mk_Vari a) in
    let impls = mk_Arro (term_T_a, mk_Arro (term_T_a, term_Prop)) in
    mk_Prod (term_U, bind_var a impls)
  in
  register_builtin "eq" expected_eq_type;
  let expected_refl_type pos map =
    (* [Π (a:U) (x:T a), P (eq a x x)] *)
    let symb_T = Builtin.get pos map "T" in
    let symb_P = Builtin.get pos map "P" in
    let symb_eq = Builtin.get pos map "eq" in
    let term_U = get_domain_of_type symb_T in
    let a = new_var "a" in
    let x = new_var "x" in
    let appl_eq = mk_Appl (mk_Symb symb_eq, mk_Vari a) in
    let appl_eq = mk_Appl (mk_Appl (appl_eq, mk_Vari x), mk_Vari x) in
    let appl = mk_Appl (mk_Symb symb_P, appl_eq) in
    let term_T_a = mk_Appl (mk_Symb symb_T, mk_Vari a) in
    let prod = mk_Prod (term_T_a, bind_var x appl) in
    mk_Prod (term_U, bind_var a prod)
  in
  register_builtin "refl" expected_refl_type;
  let expected_eqind_type pos map =
    (* [Π (a:U) (x y:T a), P (eq x y) → Π (p:T a→Prop), P (p y) → P (p x)] *)
    let symb_T = Builtin.get pos map "T" in
    let term_T = mk_Symb symb_T in
    let symb_P = Builtin.get pos map "P" in
    let term_P = mk_Symb symb_P in
    let symb_eq = Builtin.get pos map "eq" in
    let term_eq = mk_Symb symb_eq in
    let term_U = get_domain_of_type symb_T in
    let term_Prop = get_domain_of_type symb_P in
    let a = new_var "a" in
    let x = new_var "x" in
    let y = new_var "y" in
    let p = new_var "p" in
    let term_T_a = mk_Appl (term_T, mk_Vari a) in
    let term_P_p_x = mk_Appl (term_P, mk_Appl (mk_Vari p, mk_Vari x)) in
    let term_P_p_y = mk_Appl (term_P, mk_Appl (mk_Vari p, mk_Vari y)) in
    let impl = mk_Arro (term_P_p_y, term_P_p_x) in
    let prod =
      mk_Prod (mk_Arro (term_T_a, term_Prop), bind_var p impl) in
    let eq = add_args term_eq [mk_Vari a; mk_Vari x; mk_Vari y] in
    let impl = mk_Arro (mk_Appl(term_P, eq), prod) in
    let prod = mk_Prod (term_T_a, bind_var y impl) in
    let prod = mk_Prod (term_T_a, bind_var x prod) in
    mk_Prod (term_U, bind_var a prod)
  in
  register_builtin "eqind" expected_eqind_type

(** [get_eq_data pos cfg a] returns [((a,l,r),[v1;..;vn])] if [a ≡ Π v1:A1,
   .., Π vn:An, P (eq a l r)] and fails otherwise. *)
let get_eq_data :
  eq_config -> popt -> term -> (term * term * term) * var list = fun cfg ->
  let exception Not_eq of term in
  let get_eq_args u =
    if Logger.log_enabled () then log "get_eq_args %a" term u;
    match get_args u with
    | eq, [a;l;r] when is_symb cfg.symb_eq eq -> a, l, r
    | _ -> raise (Not_eq u)
  in
  let exception Not_P of term in
  let return vs r = r, List.rev vs in
  let rec get_eq vs t notin_whnf =
    if Logger.log_enabled () then log "get_eq %a" term t;
    match get_args t with
    | Prod(_,t), _ -> let v,t = unbind t in get_eq (v::vs) t true
    | p, [u] when is_symb cfg.symb_P p ->
      begin
        let u = Eval.whnf ~tags:[`NoRw;`NoExpand] [] u in
        try return vs (get_eq_args u)
        with Not_eq _ ->
          (try return vs (get_eq_args (Eval.whnf [] u))
           with Not_eq _ when notin_whnf -> get_eq vs (Eval.whnf [] t) false)
      end
    | _ ->
      if notin_whnf then get_eq vs (Eval.whnf [] t) false
      else raise (Not_P t)
  in
  fun pos t ->
    if Logger.log_enabled () then log "get_eq_data %a" term t;
    try get_eq [] t true with
    | Not_P u ->
      fatal pos "Expected %a _ but found %a." sym cfg.symb_P term u
    | Not_eq u ->
      fatal pos "Expected %a _ _ but found %a." sym cfg.symb_eq term u

(** Type of a term with the free variables that need to be substituted. It is
   usually used to store the LHS of a proof of equality, together with the
   variables that were quantified over. *)
type to_subst = var array * term

(** [matches p t] instantiates the [TRef]'s of [p] so that [p] gets equal
   to [t] and returns [true] if all [TRef]'s of [p] could be instantiated, and
   [false] otherwise. *)
let matches : term -> term -> bool =
  let exception Not_equal in
  let add_eqs = List.fold_left2 (fun l pi ti -> (pi,ti)::l) in
  let rec eq l =
    match l with
    | [] -> ()
    | (p,t)::l ->
      if Term.cmp p t = 0 then eq l else begin
      let hp, ps, kp = get_args_len p and ht, ts, kt = get_args_len t in
      if Logger.log_enabled() then
        log "matches? %a %a ≡ %a %a"
          term hp (D.list term) ps term ht (D.list term) ts;
      match hp with
      | Wild -> assert false (* used in user syntax only *)
      | Patt _ -> assert false (* used in rules only *)
      | Plac _ -> assert false (* used in scoping only *)
      | Appl _ -> assert false (* not possible after get_args_len *)
      | Type -> assert false (* not possible because of typing *)
      | Kind -> assert false (* not possible because of typing *)
      | Bvar _ -> assert false (* used in reduction only *)
      | TRef r ->
        if kp > kt then raise Not_equal;
        let ts1, ts2 = List.cut ts (kt-kp) in
        let u = add_args ht ts1 in
        if Logger.log_enabled() then log (Color.red "<TRef> ≔ %a") term u;
        Timed.(r := Some u);
        eq (add_eqs l ps ts2)
      | Meta _ -> eq l (* We assume that metas can always be instantiated by
                          the corresponding RHS although this might not be the
                          case, in which case tac_refine or solve will later
                          fail. This way, we may chose the wrong subterm. *)
      | Prod _
      | Abst _
      | LLet _
      | Symb _
      | Vari _ ->
        if kp <> kt then raise Not_equal;
        match hp, ht with
        | Vari x, Vari y when eq_vars x y -> eq (add_eqs l ps ts)
        | Symb f, Symb g when f == g -> eq (add_eqs l ps ts)
        | Abst(a,b), Abst(a',b')
        | Prod(a,b), Prod(a',b') ->
            let _,b,b' = unbind2 b b' in
            eq ((a,a')::(b,b')::add_eqs l ps ts)
        | LLet(a,c,b), LLet(a',c',b') ->
            let _,b,b' = unbind2 b b' in
            eq ((a,a')::(c,c')::(b,b')::add_eqs l ps ts)
        | _ ->
          if Logger.log_enabled() then log "distinct heads";
          raise Not_equal
      end
  in
  fun p t ->
  let r = try eq [p,t]; true with Not_equal -> false in
  if Logger.log_enabled() then log "matches result: %b" r; r

let no_match ?(subterm=false) pos (*g_env*) (vars,p) t =
  (* Rename [vars] with names distinct from those of [g_env] and [t]. *)
  (*let f idmap x =
    let name, idmap = Name.get_safe_prefix (base_name x) idmap in
    idmap, mk_Vari (new_var name)
  in
  let ts = snd (Array.fold_left_map f (Env.names g_env) vars) in*)
  let ts = Array.map (fun v -> mk_Vari (new_var ("$"^base_name v))) vars in
  let p = msubst (bind_mvar vars p) ts in
  if subterm then fatal pos "No subterm of [%a] matches [%a]." term t term p
  else fatal pos "[%a] doesn't match [%a]." term t term p

(** [matching_subs (xs,p) t] attempts to match the pattern [p] containing the
   variables [xs]) with the term [t]. If successful, it returns [Some ts]
   where [ts] is an array of terms such that substituting [xs] by the
   corresponding elements of [ts] in [p] yields [t].

WARNING: Some elements of [ts] may be uninstantiated TRef's. It will happen if
not all [vars] are in [LibTerm.free_vars p], for instance when some [vars] are
type variables not occurring in [p], for instance when trying to apply an
equation of the form [x = ...] with [x] of polymorphic type. This could be
improved by generating p_terms instead of terms. Indeed, in this case, we
could replace uninstantiated TRef's by underscores. *)
let matching_subs : to_subst -> term -> term array option = fun (xs,p) t ->
  (* We replace [xs] by fresh [TRef]'s. *)
  let ts = Array.map (fun _ -> mk_TRef(Timed.ref None)) xs in
  let p = msubst (bind_mvar xs p) ts in
  if matches p t then Some ts else None

(** [check_subs vars ts] check that no element of [ts] is an uninstantiated
    TRef. *)
let check_subs pos vars ts =
  let f i ti =
    match unfold ti with
    | TRef _ ->
        fatal pos "Don't know how to instantiate the argument \"%a\" \
                   of the equation." var vars.(i)
    | _ -> ()
  in
  Array.iteri f ts

let matching_subs_check_TRef pos ((vars,_) as xsp) t =
  match matching_subs xsp t with
  | Some ts -> check_subs pos vars ts; ts
  | None -> no_match pos xsp t

(** [find_subst (xs,p) t] tries to find the first instance of a subterm of [t]
   matching [p]. If successful, the function returns the array of terms by
   which [xs] must be substituted. *)
let find_subst : to_subst -> term -> term array option = fun xsp t ->
  let time = Timed.Time.save () in
  let rec find : term -> term array option = fun t ->
    if Logger.log_enabled() then
      log "find_subst %a ≡ %a" term (snd xsp) term t;
    match matching_subs xsp t with
    | None ->
        begin
          Timed.Time.restore time;
          match unfold t with
            | Appl(a,b) -> find2 a b
            | Abst(a,b) | Prod(a,b) -> let _,b = unbind b in find2 a b
            | LLet(a,c,b) -> let _,b = unbind b in find3 a c b
            | _ -> None
        end
    | sub -> sub
  and find2 a b =
    match find a with
    | None -> Timed.Time.restore time; find b
    | sub -> sub
  and find3 a b c =
    match find a with
    | None -> Timed.Time.restore time; find2 b c
    | sub -> sub
  in find t

let find_subst pos (vars,p) t =
  match find_subst (vars,p) t with
  | None -> no_match ~subterm:true pos (vars,p) t
  | Some ts -> check_subs pos vars ts; ts

(** [find_subterm_matching p t] tries to find a subterm of [t] that matches
   [p] by instantiating the [TRef]'s of [p].  In case of success, the function
   returns [true]. *)
let find_subterm_matching : term -> term -> bool = fun p t ->
  let time = Timed.Time.save () in
  let rec find : term -> bool = fun t ->
    matches p t ||
      begin
        Timed.Time.restore time;
        match unfold t with
        | Appl(a,b) -> find2 a b
        | Abst(a,b) | Prod(a,b) -> let _,b = unbind b in find2 a b
        | LLet(a,c,b) -> let _,b = unbind b in find3 a c b
        | _ -> false
      end
  and find2 a b =
    match find a with
    | false -> Timed.Time.restore time; find b
    | true  -> true
  and find3 a c b =
    match find a with
    | false -> Timed.Time.restore time; find2 c b
    | true -> true
  in find t

(** [replace_wild_by_tref t] substitutes every wildcard of [t] by a fresh
   [TRef]. *)
let rec replace_wild_by_tref : term -> term = fun t ->
  match unfold t with
  | Wild -> mk_TRef(Timed.ref None)
  | Appl(t,u) ->
    mk_Appl_not_canonical(replace_wild_by_tref t, replace_wild_by_tref u)
  | _ -> t

let find_subterm_matching pos p t =
  let p_refs = replace_wild_by_tref p in
  if not (find_subterm_matching p_refs t) then
    no_match ~subterm:true pos ([||],p) t;
  p_refs

(** [bind_pattern p t] replaces in the term [t] every occurence of the pattern
   [p] by a fresh variable, and returns the binder on this variable. *)
let bind_pattern : term -> term -> binder =  fun p t ->
  let z = new_var "z" in
  let rec replace : term -> term = fun t ->
    if matches p t then mk_Vari z else
    match unfold t with
    | Appl(t,u) -> mk_Appl (replace t, replace u)
    | Prod(a,b) ->
        let x,b = unbind b in
        mk_Prod (replace a, bind_var x (replace b))
    | Abst(a,b) ->
        let x,b = unbind b in
        mk_Abst (replace a, bind_var x (replace b))
    | LLet(typ, def, body) ->
        let x, body = unbind body in
        mk_LLet (replace typ, replace def, bind_var x (replace body))
    | Meta(m,ts) -> mk_Meta (m, Array.map replace ts)
    | Bvar _ -> assert false
    | Wild -> assert false
    | TRef _ -> assert false
    | Patt _ -> assert false
    | Plac _ -> assert false
    | _ -> t
  in
  bind_var z (replace t)

(** [swap cfg a r l t] returns a term of type [P (eq a l r)] from a term [t]
   of type [P (eq a r l)]. *)
let swap : eq_config -> term -> term -> term -> term -> term =
  fun cfg a r l t ->
  (* We build the predicate “λx:T a, eq a l x”. *)
  let pred =
    let x = new_var "x" in
    let pred = add_args (mk_Symb cfg.symb_eq) [a; l; mk_Vari x] in
    mk_Abst(mk_Appl(mk_Symb cfg.symb_T, a), bind_var x pred)
  in
  (* We build the proof term. *)
  let refl_a_l = add_args (mk_Symb cfg.symb_refl) [a; l] in
  add_args (mk_Symb cfg.symb_eqind) [a; r; l; t; pred; refl_a_l]

(** [rewrite ss p pos gt l2r pat t] generates a term for the refine tactic
   representing the application of the rewrite tactic to the goal type
   [gt]. Every occurrence of the first instance of the left-hand side is
   replaced by the right-hand side of the obtained proof (or the reverse if
   l2r is false). [pat] is an optional SSReflect pattern. [t] is the
   equational lemma that is appied. It handles the full set of SSReflect
   patterns. *)
let rewrite : Sig_state.t -> problem -> popt -> goal_typ -> bool ->
              (term, binder) Parsing.Syntax.rw_patt option -> term -> term =
  fun ss p pos {goal_hyps=g_env; goal_type=g_type; _} l2r pat t ->

  (* Obtain the required symbols from the current signature. *)
  let cfg = get_eq_config ss pos in

  (* Extract the term from the goal type (get “u” from “P u”). *)
  let g_term =
    match get_args g_type with
    | t, [u] when is_symb cfg.symb_P t -> u
    | _ -> fatal pos "Goal not of the form (%a _)." sym cfg.symb_P
  in

  (* Infer the type of [t] (the argument given to the tactic). *)
  let g_ctxt = Env.to_ctxt g_env in
  let (t, t_type) = Query.infer pos p g_ctxt t in

  (* Check that [t_type ≡ Π x1:a1, ..., Π xn:an, P (eq a l r)]. *)
  let (a, l, r), vars = get_eq_data cfg pos t_type in
  let vars = Array.of_list vars in

  (* Apply [t] to the variables of [vars] to get a witness of the equality. *)
  let t = Array.fold_left (fun t x -> mk_Appl(t, mk_Vari x)) t vars in

  (* Reverse the members of the equation if l2r is false. *)
  let (t, l, r) = if l2r then (t, l, r) else (swap cfg a l r t, r, l) in

  (* Bind the variables in this new witness. *)
  let bound = let bind = bind_mvar vars in bind t, bind l, bind r in
  let msubst3 (b1, b2, b3) ts = msubst b1 ts, msubst b2 ts, msubst b3 ts in

  (* Obtain the different components depending on the pattern. *)
  let (pred_bind, new_term, t, l, r) =
    match pat with
    (* Simple rewrite, no pattern. *)
    | None ->
        (* Build a substitution from the first instance of [l] in the goal. *)
        let sigma = find_subst pos (vars, l) g_term in
        (* Build the required data from that substitution. *)
        let (t, l, r) = msubst3 bound sigma in
        let pred_bind = bind_pattern l g_term in
        (pred_bind, subst pred_bind r, t, l, r)

    (* Basic patterns. *)
    | Some(Rw_Term(p)) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p = find_subterm_matching pos p g_term in
        (* Build a substitution by matching [match_p] with the LHS [l]. *)
        let sigma = matching_subs_check_TRef pos (vars,l) match_p in
        (* Build the data from the substitution. *)
        let (t, l, r) = msubst3 bound sigma in
        let pred_bind = bind_pattern l g_term in
        (pred_bind, subst pred_bind r, t, l, r)

    (* Nested patterns. *)
    | Some(Rw_InTerm(p)) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p = find_subterm_matching pos p g_term in
        (* Build a substitution from a subterm of [match_p] matching [l]. *)
        let sigma = find_subst pos (vars,l) match_p in
        (* Build the data from the substitution. *)
        let (t, l, r) = msubst3 bound sigma in
        let p_x = bind_pattern l match_p in
        let p_r = subst p_x r in
        let pred_bind = bind_pattern match_p g_term in
        let new_term = subst pred_bind p_r in
        let (x, p_x) = unbind p_x in
        let pred = subst pred_bind p_x in
        let pred_bind = bind_var x pred in
        (pred_bind, new_term, t, l, r)

    | Some(Rw_IdInTerm(p)) ->
        (* The code here works as follows: *)
        (* 1 - Try to match [p] with some subterm of the goal. *)
        (* 2 - If we succeed we do two things, we first replace [id] with its
               value, [id_val], the value matched to get [pat_l] and  try to
               match [id_val] with the LHS of the lemma. *)
        (* 3 - If we succeed we create the "RHS" of the pattern, which is [p]
               with [sigma r] in place of [id]. *)
        (* 4 - We then construct the following binders:
               a - [pred_bind_l] : A binder with a new variable replacing each
                   occurrence of [pat_l] in g_term.
               b - [pred_bind] : A binder with a new variable only replacing
                   the subterms where a rewrite happens. *)
        (* 5 - The new goal [new_term] is constructed by substituting [r_pat]
               in [pred_bind_l]. *)
        let (id,p) = unbind p in
        let p_refs = replace_wild_by_tref p in
        let sigma = find_subst pos ([|id|],p_refs) g_term in
        let id_val = sigma.(0) in
        let pat = bind_var id p_refs in
        (* The LHS of the pattern, i.e. the pattern with id replaced by *)
        (* id_val. *)
        let pat_l = subst pat id_val in

        (* This must match with the LHS of the equality proof we use. *)
        let sigma = matching_subs_check_TRef pos (vars,l) id_val in
        (* Build t, l, using the substitution we found. Note that r  *)
        (* corresponds to the value we get by applying rewrite to *)
        (* id val. *)
        let (t,l,r) = msubst3 bound sigma in

        (* The RHS of the pattern, i.e. the pattern with id replaced *)
        (* by the result of rewriting id_val. *)
        let pat_r = subst pat r in

        (* Build the predicate, identifying all occurrences of pat_l *)
        (* substituting them, first with pat_r, for the new goal and *)
        (* then with l_x for the lambda term. *)
        let pred_bind_l = bind_pattern pat_l g_term in

        (* This will be the new goal. *)
        let new_term = subst pred_bind_l pat_r in

        (* [l_x] is the pattern with [id] replaced by the variable X *)
        (* that we use for building the predicate. *)
        let (x, l_x) = unbind pat in
        let pred_bind = bind_var x (subst pred_bind_l l_x) in
        (pred_bind, new_term, t, l, r)

    (* Combinational patterns. *)
    | Some(Rw_TermInIdInTerm(s,p)) ->
        (* This pattern combines the previous.  First, we identify the subterm
           of [g_term] that matches with [p] where [p] contains an identifier.
           Once we have the value that the identifier in [p] has been  matched
           to, we find a subterm of it that matches with [s].  Then in all the
           occurrences of the first instance of [p] in [g_term] we rewrite all
           occurrences of the first instance of [s] in the subterm of [p] that
           was matched with the identifier. *)
        let (id,p) = unbind p in
        let p_refs = replace_wild_by_tref p in
        let sigma = find_subst pos ([|id|],p_refs) g_term in
        (* Once we get the value of id, we work with that as our main term
           since this is where s will appear and will be substituted in. *)
        let id_val = sigma.(0) in
        (* [pat] is the full value of the pattern, with the wildcards now
           replaced by subterms of the goal and [id]. *)
        let pat = bind_var id p_refs in
        let pat_l = subst pat id_val in

        (* We then try to match the wildcards in [s] with subterms of
           [id_val]. *)
        let s = find_subterm_matching pos s id_val in

        (* Now we must match s, which no longer contains any TRef's
           with the LHS of the lemma. *)
        let sigma = matching_subs_check_TRef pos (vars,l) s in
        let (t,l,r) = msubst3 bound sigma in

        (* First we work in [id_val], that is, we substitute all
           the occurrences of [l] in [id_val] with [r]. *)
        let id_bind = bind_pattern l id_val in

        (* [new_id] is the value of [id_val] with [l] replaced
           by [r] and [id_x] is the value of [id_val] with the
           free variable [x]. *)
        let new_id = subst id_bind r in
        let (x, id_x) = unbind id_bind in

        (* Then we replace in pat_l all occurrences of [id]
           with [new_id]. *)
        let pat_r = subst pat new_id in

        (* To get the new goal we replace all occurrences of
          [pat_l] in [g_term] with [pat_r]. *)
        let pred_bind_l = bind_pattern pat_l g_term in

        (* [new_term] is the type of the new goal meta. *)
        let new_term = subst pred_bind_l pat_r in

        (* Finally we need to build the predicate. First we build
           the term l_x, in a few steps. We substitute all the
           rewrites in new_id with x and we repeat some steps. *)
        let l_x = subst pat id_x in

        (* The last step to build the predicate is to substitute
           [l_x] everywhere we find [pat_l] and bind that x. *)
        let pred = subst pred_bind_l l_x in
        (bind_var x pred, new_term, t, l, r)

    | Some(Rw_TermAsIdInTerm(s,p)) ->
        (* This pattern is essentially a let clause.  We first match the value
           of [pat] with some subterm of the goal, and then rewrite in each of
           the occurences of [id]. *)
        let (id,pat) = unbind p in
        let s = replace_wild_by_tref s in
        let p_s = subst p s in
        (* Try to match p[s/id] with a subterm of the goal. *)
        let p = find_subterm_matching pos p_s g_term in
        let pat_refs = replace_wild_by_tref pat in
        (* Here we have already asserted tat an instance of p[s/id] exists
           so we know that this will match something. The step is repeated
           in order to get the value of [id]. *)
        let sub = matching_subs_check_TRef pos ([|id|],pat_refs) p in
        let id_val = sub.(0) in
        (* This part of the term-building is similar to the previous
           case, as we are essentially rebuilding a term, with some
           subterms that are replaced by new ones. *)
        let sigma = matching_subs_check_TRef pos (vars,l) id_val in
        let (t,l,r) = msubst3 bound sigma in

        (* Now to do some term building. *)
        let p_x = bind_pattern l p in
        let p_r = subst p_x r in
        let pred_bind = bind_pattern p g_term in
        let new_term = subst pred_bind p_r in
        let (x, p_x) = unbind p_x in
        let pred_bind = bind_var x (subst pred_bind p_x) in
        (pred_bind, new_term, t, l, r)

    | Some(Rw_InIdInTerm(q)) ->
        (* This is very similar to the [Rw_IdInTerm] case. Instead of matching
           [id_val] with [l],  we try to match a subterm of [id_val] with [l],
           and then we rewrite this subterm. As a consequence,  we just change
           the way we construct a [pat_r]. *)
        let (id,q) = unbind q in
        let q_refs = replace_wild_by_tref q in
        let sigma = find_subst pos ([|id|],q_refs) g_term in
        let id_val = sigma.(0) in
        let pat = bind_var id q_refs in
        let pat_l = subst pat id_val in
        let sigma = find_subst pos (vars,l) id_val in
        let (t,l,r) = msubst3 bound sigma in

        (* Rewrite in id. *)
        let id_bind = bind_pattern l id_val in
        let id_val = subst id_bind r in
        let (x, id_x) = unbind id_bind in

        (* The new RHS of the pattern is obtained by rewriting in [id_val]. *)
        let r_val = subst pat id_val in
        let pred_bind_l = bind_pattern pat_l g_term in
        let new_term = subst pred_bind_l r_val in
        let l_x = subst pat id_x in
        let pred_bind = bind_var x (subst pred_bind_l l_x) in
        (pred_bind, new_term, t, l, r)
  in

  (* Construct the predicate (context). *)
  let pred = mk_Abst(mk_Appl(mk_Symb cfg.symb_T, a), pred_bind) in

  (* Construct the new goal and its type. *)
  let goal_type = mk_Appl(mk_Symb cfg.symb_P, new_term) in
  let goal_term = LibMeta.make p g_ctxt goal_type in

  (* Build the final term produced by the tactic. *)
  let eqind = mk_Symb cfg.symb_eqind in
  let result = add_args eqind [a; l; r; t; pred; goal_term] in

  (* Debugging data to the log. *)
  if Logger.log_enabled () then
    begin
      log "Rewriting with:";
      log "  goal           = [%a]" term g_type;
      log "  equality proof = [%a]" term t;
      log "  equality LHS   = [%a]" term l;
      log "  equality RHS   = [%a]" term r;
      log "  pred           = [%a]" term pred;
      log "  new goal       = [%a]" term goal_type;
      log "  produced term  = [%a]" term result;
    end;

  (* Return the proof-term. *)
  result
