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

(** [subst_from_constrs cs] builds a //typing substitution// from the list  of
    constraints [cs]. The returned substitution is given by a couple of arrays
    [(xs,ts)] of the same length.  The array [xs] contains the variables to be
    substituted using the terms of [ts] at the same index. *)
let subst_from_constrs : unif_constrs -> subst = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []          -> List.split acc
    | (_,a,b)::cs ->
      match Basics.get_args a with
      | Vari(x), [] -> build_sub ((x,b)::acc) cs
      | _, _ ->
        match Basics.get_args b with
        | Vari(x), [] -> build_sub ((x,a)::acc) cs
        | _, _ -> build_sub acc cs
  in
  let (vs,ts) = build_sub [] cs in
  (Array.of_list vs, Array.of_list ts)

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
let check_rule : sym StrMap.t -> sym * pp_hint * rule Pos.loc -> unit =
    fun builtins (s,h,r) ->
  if !log_enabled then log_subj "check_rule [%a]" pp_rule (s, h, r.elt);
  (* We process the LHS to replace pattern variables by metavariables. *)
  let binder_arity = Bindlib.mbinder_arity r.elt.rhs in
  let metas = Array.make binder_arity None in
  let rec to_m : int -> term -> tbox = fun k t ->
    (* [k] is the number of arguments to which [m] is applied. *)
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s,h)   -> _Symb s h
    | Abst(a,t)   -> let (x,t) = Bindlib.unbind t in
                     _Abst (to_m 0 a) (Bindlib.bind_var x (to_m 0 t))
    | LLet(t,a,u) ->
        let (x, u) = Bindlib.unbind u in
        _LLet (to_m 0 t) (to_m 0 a) (Bindlib.bind_var x (to_m 0 u))
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
    | Meta(_,_)   -> assert false (* Cannot appear in LHS. *)
    | TEnv(_,_)   -> assert false (* Cannot appear in LHS. *)
    | Wild        -> assert false (* Cannot appear in LHS. *)
    | TRef(_)     -> assert false (* Cannot appear in LHS. *)
  in
  let lhs = List.map (fun p -> Bindlib.unbox (to_m 0 p)) r.elt.lhs in
  let lhs = Basics.add_args (Symb(s,h)) lhs in
  let metas = Array.map (function Some m -> m | None -> assert false) metas in
  (* We substitute the RHS with the corresponding metavariables. *)
  let fn m =
    let xs = Array.init m.meta_arity (Printf.sprintf "x%i") in
    let xs = Bindlib.new_mvar mkfree xs in
    let e = Array.map _Vari xs in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m e)))
  in
  let te_envs = Array.map fn metas in
  let rhs = Bindlib.msubst r.elt.rhs te_envs in
  (* Infer the type of the LHS and the constraints. *)
  match Typing.infer_constr builtins [] lhs with
  | None                      -> wrn r.pos "Untypable LHS."
  | Some(ty_lhs, lhs_constrs) ->
  if !log_enabled then
    begin
      log_subj "LHS has type [%a]" pp ty_lhs;
      let fn (c,t,u) = log_subj "  if %a[%a] ~ [%a]" wrap_ctxt c pp t pp u in
      List.iter fn lhs_constrs
    end;
  (* Turn constraints into a substitution and apply it. *)
  let (xs,ts) = subst_from_constrs lhs_constrs in
  let p = Bindlib.box_pair (lift rhs) (lift ty_lhs) in
  let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
  let (rhs,ty_lhs) = Bindlib.msubst p ts in
  (* Check that the RHS has the same type as the LHS. *)
  let to_solve = Infer.check [] rhs ty_lhs in
  if !log_enabled && to_solve <> [] then
    begin
      log_subj "RHS has type [%a]" pp ty_lhs;
      List.iter (log_subj "  if %a" pp_constr) to_solve
    end;
  (* Solving the constraints. *)
  match Unif.(solve builtins false {no_problems with to_solve}) with
  | None     ->
      fatal r.pos "Rule [%a] does not preserve typing." pp_rule (s,h,r.elt)
  | Some(cs) ->
  let is_constr c =
    let eq_comm (c1,t1,u1) (c2,t2,u2) =
      let ctx = match Ctxt.merge c1 c2 with None -> [] | Some(x) -> x in
      (Eval.eq_modulo ctx t1 t2 && Eval.eq_modulo ctx u1 u2) ||
      (Eval.eq_modulo ctx t1 u2 && Eval.eq_modulo ctx t2 u1)
    in
    List.exists (eq_comm c) lhs_constrs
  in
  let cs = List.filter (fun c -> not (is_constr c)) cs in
  if cs <> [] then
    begin
      List.iter (fatal_msg "Cannot solve %a\n" pp_constr) cs;
      fatal r.pos "Unable to prove SR for rule [%a]." pp_rule (s,h,r.elt)
    end;
  (* Check that there is no uninstanciated metas left. *)
  let lhs_metas = Basics.get_metas false lhs in
  let f m =
    if not (List.in_sorted cmp_meta m lhs_metas) then
      fatal r.pos "Cannot instantiate all metavariables in rule [%a]."
        pp_rule (s,h,r.elt)
  in
  Basics.iter_meta false f rhs
