(** Type-checking and inference. *)

open Timed
open Console
open Terms
open Print
open Extra

(** Logging function for typing. *)
let log_subj = new_logger 's' "subj" "subject-reduction"
let log_subj = log_subj.logger

(** Representation of a substitution. *)
type subst = tvar array * term array

(** [build_meta_type k] builds the type “∀(x1:A1) ⋯ (xk:Ak), A(k+1)” where the
    type “Ai = Mi[x1,⋯,x(i-1)]” is defined as the metavariable “Mi” (which has
    arity “i-1”). The type of “Mi” is “∀(x1:A1) ⋯ (x(i-1):A(i-1)), TYPE”. *)
let build_meta_type : int -> term = fun k ->
  assert (k >= 0);
  (* We create the variables “xi”. *)
  let xs = Bindlib.new_mvar mkfree (Array.init k (Printf.sprintf "x%i")) in
  (* We also make a boxed version of the variables. *)
  let ts = Array.map _Vari xs in
  (* We create the types for the “Mi” metavariables. *)
  let ty_m = Array.make (k+1) _Type in
  for i = 0 to k do
    for j = (i-1) downto 0 do
      ty_m.(i) <- _Prod ty_m.(j) (Bindlib.bind_var xs.(j) ty_m.(i))
    done
  done;
  (* We create the “Ai” terms (and the “Mi” metavariables). *)
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
  if !log_enabled then log_subj "check_rule [%a]" pp_rule (s, h, rule);
  let binder_arity = Bindlib.mbinder_arity rule.rhs in
  (* Compute the metavariables of the RHS, including the metavariables of
     their types. *)
  let rhs_metas =
    Basics.get_metas true
      (Bindlib.msubst rule.rhs (Array.make binder_arity TE_None))
  in
  (* We process the LHS to replace pattern variables by metavariables. *)
  let metas = Array.make binder_arity None in
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
              match metas.(i) with
              | Some(m) -> _Meta m a
              | None    ->
                 let m = fresh_meta ~name:n (build_meta_type (l+k)) l in
                 metas.(i) <- Some(m);
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
  let metas = Array.map (function Some m -> m | None -> assert false) metas in
  (* Infer the type of the LHS and the constraints. *)
  match Typing.infer_constr builtins [] lhs with
  | None                      -> wrn pos "Untypable LHS."; shrp
  | Some(ty_lhs, lhs_constrs) ->
  if !log_enabled then
    begin
      log_subj "LHS has type %a" pp ty_lhs;
      List.iter (log_subj "  if %a" pp_constr) lhs_constrs
    end;
  (* We substitute the RHS with the corresponding metavariables. *)
  let fn m =
    let ns = Array.init m.meta_arity (Printf.sprintf "x%i") in
    let xs = Bindlib.new_mvar mkfree ns in
    let e = Array.map _Vari xs in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m e)))
  in
  let te_envs = Array.map fn metas in
  let subst t = Bindlib.msubst t te_envs in
  let rhs = subst rule.rhs in
  (* We substitute the metavariables of the RHS as well. *)
  let fn m =
    let bt = lift !(m.meta_type) in
    m.meta_type := subst (Bindlib.unbox (Bindlib.bind_mvar rule.vars bt))
  in
  MetaSet.iter fn rhs_metas;
  (* Here, we should instantiate the LHS metas by fresh function symbols and
     complete the constraints into a set of rewriting rules on those function
     symbols. *)
  (* Check that the RHS has the same type as the LHS. *)
  let to_solve = Infer.check [] rhs ty_lhs in
  if !log_enabled && to_solve <> [] then
    begin
      log_subj "RHS has type %a" pp ty_lhs;
      List.iter (log_subj "  if %a" pp_constr) to_solve
    end;
  (* Solving the constraints. To help resolution, metavariable symbols having
     no constraint could be replaced by fresh variables. *)
  match Unif.(solve builtins false {no_problems with to_solve}) with
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
      fatal pos "Unable to prove SR for rule [%a]." pp_rule (s,h,rule)
    end;
  (* Check that there is no uninstanciated metas left. *)
  let lhs_metas = Basics.get_metas false lhs in
  let f m =
    if not (MetaSet.mem m lhs_metas) then
      fatal pos "Cannot instantiate all metavariables in rule [%a]."
        pp_rule (s,h,rule)
  in
  Basics.iter_meta false f rhs;
  (* Return rule with metavariables instanciated. We need to replace
     metavariables by term_env variables, and bind them. *)
  let new_rhs = rule.rhs in
  (*Bindlib.unbox (Bindlib.bind_mvar rule.vars (lift rhs))*)
  let new_rule = { rule with rhs = new_rhs } in
  (s, h, { elt = new_rule; pos = pos })
