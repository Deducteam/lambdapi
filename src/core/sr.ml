(** Type-checking and inference. *)

open Timed
open Console
open Terms
open Print
open Extra

(** Logging function for typing. *)
let log_subj = new_logger 's' "subj" "subject-reduction"
let log_subj = log_subj.logger

(** [build_meta_type k] builds the type “∀x1:A1,⋯,xk:Ak,A(k+1)” where the
    type “Ai = Mi[x1,⋯,x(i-1)]” is defined as the metavariable “Mi” which has
    arity “i-1” and type “∀(x1:A1) ⋯ (x(i-1):A(i-1)), TYPE”. *)
let build_meta_type : int -> term = fun k ->
  assert (k >= 0);
  let xs = Basics.fresh_vars k in
  let ts = Array.map _Vari xs in
  (* We create the types for the “Mi” metavariables. *)
  let ty_m = Array.make (k+1) _Type in
  for i = 0 to k do
    for j = (i-1) downto 0 do
      ty_m.(i) <- _Prod ty_m.(j) (Bindlib.bind_var xs.(j) ty_m.(i))
    done
  done;
  (* We create the “Ai” terms and the “Mi” metavariables. *)
  let fn i =
    let m = fresh_meta (Bindlib.unbox ty_m.(i)) i in
    _Meta m (Array.sub ts 0 i)
  in
  let a = Array.init (k+1) fn in
  (* We finally construct our type. *)
  let res = ref a.(k) in
  for i = k - 1 downto 0 do
    res := _Prod a.(i) (Bindlib.bind_var xs.(i) !res)
  done;
  Bindlib.unbox !res

(** [check_rule builtins r] checks whether rule [r] is well-typed. The [Fatal]
    exception is raised in case of error. *)
let check_rule : sym StrMap.t -> sym * pp_hint * rule Pos.loc
                              -> sym * pp_hint * rule Pos.loc =
    fun builtins ((s, h, { elt = rule; pos = pos }) as shrp) ->
  if !log_enabled then log_subj (mag "check rule %a") pp_rule (s, h, rule);

  let binder_arity = Bindlib.mbinder_arity rule.rhs in
  (* Compute the metavariables of the RHS, including the metavariables of
     their types. *)
  let rhs_metas =
    Basics.get_metas true
      (Bindlib.msubst rule.rhs (Array.make binder_arity TE_None))
  in

  (* We process the LHS to replace pattern variables by metavariables. *)
  let lhs_metas = Array.make binder_arity None in
  let rec to_m : int -> term -> tbox = fun k t ->
    (* [k] is the number of arguments to which [m] is applied. *)
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s,h)   -> _Symb s h
    | Abst(a,t)   -> let (x,t) = Bindlib.unbind t in
                     _Abst (to_m 0 a) (Bindlib.bind_var x (to_m 0 t))
    | Appl(t,u)   -> _Appl (to_m (k+1) t) (to_m 0 u)
    | Patt(i,n,a) ->
        begin
          let a = Array.map (to_m 0) a in
          let l = Array.length a in
          match i with
          | None    ->
             let m = fresh_meta ~name:n (build_meta_type (l+k)) l in
             _Meta m a
          | Some(i) ->
              match lhs_metas.(i) with
              | Some(m) -> _Meta m a
              | None    ->
                 let m = fresh_meta ~name:n (build_meta_type (l+k)) l in
                 lhs_metas.(i) <- Some(m);
                 _Meta m a
        end
    | Type        -> assert false (* Cannot appear in LHS. *)
    | Kind        -> assert false (* Cannot appear in LHS. *)
    | Prod(_,_)   -> assert false (* Cannot appear in LHS. *)
    | LLet(_,_,_) -> assert false (* Cannot appear in LHS. *)
    | Meta(_,_)   -> assert false (* Cannot appear in LHS. *)
    | TEnv(_,_)   -> assert false (* Cannot appear in LHS. *)
    | Wild        -> assert false (* Cannot appear in LHS. *)
    | TRef(_)     -> assert false (* Cannot appear in LHS. *)
  in
  let lhs_args = List.map (fun p -> Bindlib.unbox (to_m 0 p)) rule.lhs in
  let lhs = Basics.add_args (Symb(s,h)) lhs_args in
  let lhs_metas =
    Array.map (function Some m -> m | None -> assert false) lhs_metas
  in

  (* Build a map LHS pattern variable -> term_env variable. *)
  let map =
    let map = ref StrMap.empty in
    let fn i m =
      map := StrMap.add (meta_name m) (rule.vars.(i), m.meta_arity) !map
    in
    Array.iteri fn lhs_metas;
    !map
  in

  (* Infer the typing constraints of the LHS. *)
  match Typing.infer_constr builtins [] lhs with
  | None                      -> wrn pos "Untypable LHS."; shrp
  | Some(ty_lhs, lhs_constrs) ->
  if !log_enabled then
    begin
      log_subj (gre "LHS has type %a") pp ty_lhs;
      List.iter (log_subj "  if %a" pp_constr) lhs_constrs
    end;

  (* We apply the mapping pattern variable -> metavariable to the RHS and the
     types of its metavariables. *)
  let fn m =
    let xs = Basics.fresh_vars m.meta_arity in
    let ts = Array.map _Vari xs in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m ts)))
  in
  let te_envs = Array.map fn lhs_metas in
  let subst t = Bindlib.msubst t te_envs in
  let rhs = subst rule.rhs in
  log_subj "rhs %a" pp_term rhs;
  let fn m =
    let bt = lift !(m.meta_type) in
    m.meta_type := subst (Bindlib.unbox (Bindlib.bind_mvar rule.vars bt))
  in
  MetaSet.iter fn rhs_metas;

  (* We compute the set of all uninstantiated metavariables of the LHS,
     including in the types of LHS metavariables. *)
  let all_lhs_metas =
    let open MetaSet in
    let add_metas m ms =
      match !(m.meta_value) with
      | Some _ ->
          let t = Meta(m, Array.make m.meta_arity Kind) in
          Basics.add_metas true t ms
      | None   -> add m (Basics.add_metas true !(m.meta_type) ms)
    in
    Array.fold_right add_metas lhs_metas empty
  in
  (* We instantiate these metavariables by fresh function symbols. *)
  let instantiate m t =
    let xs = Basics.fresh_vars m.meta_arity in
    let t = Array.fold_left (fun t x -> _Appl t (_Vari x)) t xs in
    m.meta_value := Some (Bindlib.unbox (Bindlib.bind_mvar xs t))
  in
  let fn m =
    let s = { sym_name  = meta_name m
            ; sym_type  = m.meta_type
            ; sym_path  = []
            ; sym_def   = ref None
            ; sym_impl  = []
            ; sym_rules = ref []
            ; sym_tree  = ref Tree_types.empty_dtree
            ; sym_prop  = Defin
            ; sym_expo  = Public }
    in
    instantiate m (_Symb s Nothing)
  in
  MetaSet.iter fn all_lhs_metas;

  (* Here, we should complete the constraints into a set of rewriting rules on
     those function symbols. *)
  (* TODO *)

  (* The following piece of code doesn't work as metavariables cannot be
     instantiated by terms containing free variables. *)
  (*
  (* To help resolution, metavariable symbols with no constraint are
     replaced by fresh variables. *)
  (* We compute the set of metavariables in constraints. *)
  let lhs_constrs_metas =
    let open MetaSet in
    let add_constr ms (_,l,r) =
      Basics.add_metas false l (Basics.add_metas false r ms)
    in
    List.fold_left add_constr empty lhs_constrs
  in
  let pp_metas oc = MetaSet.iter (Format.fprintf oc "%a, " pp_meta) in
  log_subj "lhs_constr_metas: %a" pp_metas lhs_constrs_metas;
  (* We compute the set of LHS metavariables having NO constraints, including
     in their types. *)
  let free_lhs_metas =
    let open MetaSet in
    let is_cstr m = mem m lhs_constrs_metas in
    let fn m ms =
      if is_cstr m || exists is_cstr (Basics.get_metas true !(m.meta_type))
      then ms
      else add m ms
    in
    MetaSet.fold fn all_lhs_metas empty
  in
  log_subj "free_lhs_metas: %a" pp_metas free_lhs_metas;
  let fn m ctx =
    let v = Bindlib.new_var mkfree (meta_name m) in
    instantiate m (_Vari v);
    (v, !(m.meta_type), None) :: ctx
  in
  let ctx = MetaSet.fold fn free_lhs_metas [] in
   *)

  (* Compute the constraints for the RHS to have the same type as the LHS. *)
  let to_solve = Infer.check [] rhs ty_lhs in
  if !log_enabled && to_solve <> [] then
    begin
      log_subj (gre "RHS has type %a") pp ty_lhs;
      List.iter (log_subj "  if %a" pp_constr) to_solve
    end;

  (* Solving the typing constraints of the RHS. *)
  match Unif.(solve builtins {no_problems with to_solve}) with
  | None     ->
      fatal pos "Rule [%a] does not preserve typing." pp_rule (s,h,rule)
  | Some(cs) ->
  let is_constr c =
    let eq_comm (_,t1,u1) (_,t2,u2) =
      (* Contexts ignored: [Infer.check] is called with an empty context and
         neither [Infer.check] nor [Unif.solve] generate contexts with defined
         variables. *)
      (Eval.eq_modulo [] t1 t2 && Eval.eq_modulo [] u1 u2) ||
      (Eval.eq_modulo [] t1 u2 && Eval.eq_modulo [] t2 u1)
    in
    List.exists (eq_comm c) lhs_constrs
  in
  let cs = List.filter (fun c -> not (is_constr c)) cs in
  if cs <> [] then
    begin
      List.iter (fatal_msg "Cannot solve %a\n" pp_constr) cs;
      fatal pos "Unable to prove type preservation for the rule %a."
        pp_rule (s,h,rule)
    end;

  (* Replace metavariable symbols by term_env variables, and bind them. *)
  let rec to_tenv t =
    log_subj "to_tenv %a" pp_term t;
    let t = unfold t in
    let h, ts = Basics.get_args t in
    let ts = List.map to_tenv ts in
    match h with
    (*| Vari(x)     -> to_tenv_patt h ts (Bindlib.name_of x)*)
    | Symb(f,_)   -> to_tenv_patt h ts f.sym_name
    | Prod(a,b)   -> Prod(to_tenv a, to_tenv_binder b)
    | Abst(a,b)   -> Basics.add_args (Abst(to_tenv a, to_tenv_binder b)) ts
    | LLet(a,t,u) ->
        Basics.add_args (LLet(to_tenv a, to_tenv t, to_tenv_binder u)) ts
    | Appl(_,_)   -> assert false
    | Meta(_,_)   -> assert false
    | Patt(_)     -> assert false
    | Wild        -> assert false
    | _           -> Basics.add_args h ts
  and to_tenv_binder b =
    let (x,b) = Bindlib.unbind b in
    Bindlib.unbox (Bindlib.bind_var x (lift (to_tenv b)))
  and to_tenv_patt h ts s =
    if s = "" || s.[0] <> '?' then Basics.add_args h ts
    else
      begin
        try
          let (v,k) = StrMap.find s map in
          let (ts1,ts2) = List.cut ts k in
          Basics.add_args (TEnv (TE_Vari v, Array.of_list ts1)) ts2
        with Not_found -> assert false
      end
  in
  log_subj "rhs %a" pp_term rhs;
  let rhs = to_tenv rhs in
  let rhs = Bindlib.unbox (Bindlib.bind_mvar rule.vars (lift rhs)) in
  let elt = { rule with rhs } in
  (s, h, { elt; pos })
