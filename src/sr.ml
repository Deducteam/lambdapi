(** Type-checking and inference. *)

open Timed
open Console
open Terms
open Print

(** Logging function for typing. *)
let log_subj = new_logger 'j' "subj" "debugging information for SR"
let log_subj = log_subj.logger


(** [subst_from_constrs cs] builds a //typing substitution// from the list  of
    constraints [cs]. The returned substitution is given by a couple of arrays
    [(xs,ts)] of the same length.  The array [xs] contains the variables to be
    substituted using the terms of [ts] at the same index. *)
let subst_from_constrs : (term * term) list -> tvar array * term array =
  let rec build_sub acc cs =
    match cs with
    | []        -> acc
    | (a,b)::cs ->
       let (ha,argsa) = get_args a and (hb,argsb) = get_args b in
       let na = List.length argsa and nb = List.length argsb in
        match (unfold ha, unfold hb) with
        | (Symb(sa), Symb(sb)) when sa == sb && na = nb && Sign.is_const sa ->
            let fn l t1 t2 = (t1,t2) :: l in
            build_sub acc (List.fold_left2 fn cs argsa argsb)
        | (Vari(x),_) when argsa = [] -> build_sub ((x,b)::acc) cs
        | (_,Vari(x)) when argsb = [] -> build_sub ((x,a)::acc) cs
        | (_,_) -> build_sub acc cs
  in
  fun cs ->
    let (vs,ts) = List.split (build_sub [] cs) in
    (Array.of_list vs, Array.of_list ts)

(* Does not work in examples/cic.dk

let build_meta_type : int -> term = fun k ->
  let m' = new_meta Type (*FIXME?*) k in
  let m_typ = Meta(m',[||]) in
  let m = new_meta m_typ k in
  Meta(m,[||])
*)

(** [build_meta_type k] builds the type [x_1:t_1 -> .. -> x_k:t_k ->
    t_{k+1}] where [x1,..,x_k] are fresh variables, [t_i =
    M_i[x_1,..,x_{i-1}]], [M_i] is a new metavariable of arity [i-1]
    and type [x_1:t_1 -> .. -> x_{i-1}:t_{i-1} -> Type]. *)
let build_meta_type : int -> term = fun k ->
  assert (k>=0);
  let vs = Bindlib.new_mvar mkfree (Array.make k "x") in
  let rec build_prod k p =
    if k = 0 then p
    else
      let k = k-1 in
      let mk_typ = Bindlib.unbox (build_prod k _Type) in
      let mk = fresh_meta mk_typ k in
      let tk = _Meta mk (Array.map _Vari (Array.sub vs 0 k)) in
      let b = Bindlib.bind_var vs.(k) p in
      let p = Bindlib.box_apply2 (fun a b -> Prod(a,b)) tk b in
      build_prod k p
  in
  let mk_typ = Bindlib.unbox (build_prod k _Type) (*FIXME?*) in
  let mk = fresh_meta mk_typ k in
  let tk = _Meta mk (Array.map _Vari vs) in
  Bindlib.unbox (build_prod k tk)

(** [check_rule r] check whether rule [r] is well-typed. The program
    fails gracefully in case of error. *)
let check_rule : sym * rule -> unit = fun (s,rule) ->
  if !log_enabled then log_subj "check_rule [%a]" pp_rule (s, rule);
  (** We process the LHS to replace pattern variables by metavariables. *)
  let arity = Bindlib.mbinder_arity rule.rhs in
  let metas = Array.init arity (fun _ -> None) in
  let rec to_m : int -> term -> tbox = fun k t ->
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s)     -> _Symb s
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
    | Meta(_,_)   -> assert false (* Cannot appear in LHS. *)
    | TEnv(_,_)   -> assert false (* Cannot appear in LHS. *)
  in
  let lhs = List.map (fun p -> Bindlib.unbox (to_m 0 p)) rule.lhs in
  let lhs = add_args (Symb(s)) lhs in
  (** We substitute the RHS with the corresponding metavariables.*)
  let fn m =
    let m = match m with Some(m) -> m | None -> assert false in
    let xs = Array.init m.meta_arity (Printf.sprintf "x%i") in
    let xs = Bindlib.new_mvar mkfree xs in
    let e = Array.map _Vari xs in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m e)))
  in
  let te_envs = Array.map fn metas in
  let rhs = Bindlib.msubst rule.rhs te_envs in
  (* Infer the type of the LHS and the constraints. *)
  match Solve.infer_constr Ctxt.empty lhs with
  | None                      -> wrn "untypable LHS\n" (* FIXME position *)
  | Some(lhs_constrs, ty_lhs) ->
  if !log_enabled then
    begin
      log_subj "[%a] : [%a]" pp lhs pp ty_lhs;
      let fn (t,u) = log_subj "  if [%a] = [%a]" pp t pp u in
      List.iter fn lhs_constrs
    end;
  (* Turn constraints into a substitution and apply it. *)
  let (xs,ts) = subst_from_constrs lhs_constrs in
  let p = Bindlib.box_pair (lift rhs) (lift ty_lhs) in
  let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
  let (rhs,ty_lhs) = Bindlib.msubst p ts in
  (* Check that the RHS has the same type as the LHS. *)
  if not (Solve.check_with_constr lhs_constrs rhs ty_lhs) then
    fatal_no_pos "Rule [%a] does not preserve typing." pp_rule (s,rule)
