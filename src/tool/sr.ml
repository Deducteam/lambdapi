(** Checking that a rule preserves typing (subject reduction property). *)

open Lplib
open Timed
open Common open Error
open Core open Term open Print
open Parsing

(** Logging function for typing. *)
let log_subj = Logger.make 's' "subj" "subject-reduction"
let log_subj = log_subj.pp

(** [build_meta_type p k] builds the type “Πx1:A1,⋯,xk:Ak,A(k+1)” where the
   type “Ai = Mi[x1,⋯,x(i-1)]” is defined as the metavariable “Mi” which has
   arity “i-1” and type “Π(x1:A1) ⋯ (x(i-1):A(i-1)), TYPE”, and adds the
   metavariables in [p]. *)
let build_meta_type : problem -> int -> term = fun p k ->
  assert (k >= 0);
  let xs = Array.init k (new_tvar_ind "x") in
  let ts = Array.map _Vari xs in
  (* We create the types for the “Mi” metavariables. *)
  let ty_m = Array.make (k+1) _Type in
  for i = 0 to k do
    for j = (i-1) downto 0 do
      ty_m.(i) <- _Prod ty_m.(j) (Bindlib.bind_var xs.(j) ty_m.(i))
    done
  done;
  (* We create the “Ai” terms and the “Mi” metavariables. *)
  let f i =
    let m = LibMeta.fresh p (Bindlib.unbox ty_m.(i)) i in
    _Meta m (Array.sub ts 0 i)
  in
  let a = Array.init (k+1) f in
  (* We finally construct our type. *)
  let res = ref a.(k) in
  for i = k - 1 downto 0 do
    res := _Prod a.(i) (Bindlib.bind_var xs.(i) !res)
  done;
  Bindlib.unbox !res

(** [patt_to_tenv vars t] converts pattern variables of [t] into corresponding
    term environment variables of [vars]. The index [i] in [Patt(Some(i),_,_)]
    indicates the index of the corresponding variable in [vars]. *)
let patt_to_tenv : tevar array -> term -> tbox = fun vars ->
  let get_te i =
    match i with
    | None    -> assert false (* Cannot appear in LHS. *)
    | Some(i) -> try vars.(i) with Invalid_argument(_) -> assert false
  in
  let rec trans t =
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s)     -> _Symb s
    | Abst(a,b)   -> let (x, b) = Bindlib.unbind b in
                     _Abst (trans a) (Bindlib.bind_var x (trans b))
    | Appl(t,u)   -> _Appl (trans t) (trans u)
    | Patt(i,_,a) -> _TEnv (_TE_Vari (get_te i)) (Array.map trans a)
    | Db _        -> assert false
    | Type        -> assert false (* Cannot appear in LHS. *)
    | Kind        -> assert false (* Cannot appear in LHS. *)
    | Prod(_,_)   -> assert false (* Cannot appear in LHS. *)
    | LLet(_,_,_) -> assert false (* Cannot appear in LHS. *)
    | Plac _      -> assert false (* Cannot appear in LHS. *)
    | Meta(_,_)   -> assert false (* Cannot appear in LHS. *)
    | TEnv(_,_)   -> assert false (* Cannot appear in LHS. *)
    | Wild        -> assert false (* Cannot appear in LHS. *)
    | TRef(_)     -> assert false (* Cannot appear in LHS. *)
  in
  trans

(** Mapping of pattern variable names to their reserved index. *)
type index_tbl = (string, int) Hashtbl.t

(** [symb_to_tenv pr syms htbl t] builds a RHS for the pre-rule [pr]. The term
    [t] is expected to be a version of the RHS of [pr] whose term environments
    have been replaced by function symbols of [syms]. This function builds the
    reverse transformation, replacing symbols by the term environment variable
    they stand for.  Here, [htbl] should give the index in the RHS environment
    for the symbols of [syms] that have corresponding [term_env] variable. The
    pre-rule [pr] is provided to give access to these variables and also their
    expected arities. *)
let symb_to_tenv
    : Scope.pre_rule Pos.loc -> sym list -> index_tbl -> term -> tbox =
  fun {elt={pr_vars=vars;pr_arities=arities;_};pos} syms htbl t ->
  let rec symb_to_tenv t =
    let (h, ts) = get_args t in
    let ts = List.map symb_to_tenv ts in
    let (h, ts) =
      match h with
      | Db _ -> assert false
      | Symb(f) when List.memq f syms ->
          let i =
            try Hashtbl.find htbl f.sym_name with Not_found ->
            (* A symbol may also come from a metavariable that appeared in the
               type of a metavariable that was replaced by a symbol. We do not
               have concrete examples of that happening yet. *)
            fatal pos "Introduced symbol [%s] cannot be removed." f.sym_name
          in
          let (ts1, ts2) = List.cut ts arities.(i) in
          (_TEnv (_TE_Vari vars.(i)) (Array.of_list ts1), ts2)
      | Symb(s)     -> (_Symb s, ts)
      | Vari(x)     -> (_Vari x, ts)
      | Type        -> (_Type  , ts)
      | Kind        -> (_Kind  , ts)
      | Abst(a,b)   ->
          let (x, t) = Bindlib.unbind b in
          let b = Bindlib.bind_var x (symb_to_tenv t) in
          (_Abst (symb_to_tenv a) b, ts)
      | Prod(a,b)   ->
          let (x, t) = Bindlib.unbind b in
          let b = Bindlib.bind_var x (symb_to_tenv t) in
          (_Prod (symb_to_tenv a) b, ts)
      | LLet(a,t,b) ->
          let (x, u) = Bindlib.unbind b in
          let b = Bindlib.bind_var x (symb_to_tenv u) in
          (_LLet (symb_to_tenv a) (symb_to_tenv t) b, ts)
      | Meta(_,_)   ->
          fatal pos "A metavariable could not be instantiated in the RHS."
      | Plac _      ->
          fatal pos "A placeholder hasn't been instantiated in the RHS."
      | TEnv(_,_)   -> assert false (* TEnv have been replaced in [t]. *)
      | Appl(_,_)   -> assert false (* Cannot appear in RHS. *)
      | Patt(_,_,_) -> assert false (* Cannot appear in RHS. *)
      | Wild        -> assert false (* Cannot appear in RHS. *)
      | TRef(_)     -> assert false (* Cannot appear in RHS. *)
    in
    _Appl_list h ts
  in
  symb_to_tenv t

(** [check_rule r] checks whether the pre-rule [r] is well-typed in
   signature state [ss] and then construct the corresponding rule. Note that
   [Fatal] is raised in case of error. *)
let check_rule : Scope.pre_rule Pos.loc -> rule = fun ({pos; elt} as pr) ->
  let Scope.{pr_sym = s; pr_lhs = lhs; pr_vars = vars; pr_rhs;
             pr_arities = arities; pr_xvars_nb; _} = elt in
  (* Check that the variables of the RHS are in the LHS. *)
  if pr_xvars_nb <> 0 then
    (let xvars = Array.drop (Array.length vars - pr_xvars_nb) vars in
     fatal pos "Unknown pattern variables: %a" (Array.pp var ",") xvars);
  let arity = List.length lhs in
  if Logger.log_enabled () then
    begin
      (* The unboxing here could be harmful since it leads to [pr_rhs] being
         unboxed twice. However things should be fine here since the result is
         only used for printing. *)
      let rhs = Bindlib.(unbox (bind_mvar vars pr_rhs)) in
      let naive_rule =
        {lhs; rhs; arity; arities; vars; xvars_nb = 0; rule_pos = pos} in
      log_subj (Color.red "%a") sym_rule (s, naive_rule);
    end;
  (* Replace [Patt] nodes of LHS with corresponding elements of [vars]. *)
  let lhs_vars = _Appl_Symb s (List.map (patt_to_tenv vars) lhs) in
  let p = new_problem() in
  let metas =
    let f i _ =
      let arity = arities.(i) in
      (*FIXME: build_meta_type should take a sort as argument as some pattern
         variables are types and thus of sort KIND! *)
      LibMeta.fresh p (build_meta_type p arity) arity
    in Array.mapi f vars
  in
  (* Substitute them in the LHS and in the RHS. *)
  let lhs_with_metas, rhs_with_metas =
    let lhs_rhs = Bindlib.box_pair lhs_vars pr_rhs in
    let b = Bindlib.unbox (Bindlib.bind_mvar vars lhs_rhs) in
    let meta_to_tenv m =
      let xs = Array.init m.meta_arity (new_tvar_ind "x") in
      let ts = Array.map _Vari xs in
      TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m ts)))
    in
    Bindlib.msubst b (Array.map meta_to_tenv metas)
  in
  if Logger.log_enabled () then
    log_subj "replace pattern variables by metavariables:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  (* Infer the typing constraints of the LHS. *)
  match Infer.infer_noexn p [] lhs_with_metas with
  | None -> fatal pos "The LHS is not typable."
  | Some (lhs_with_metas, ty_lhs) ->
  (* Try to simplify constraints. Don't check typing when instantiating
     a metavariable. *)
  if not (Unif.solve_noexn ~type_check:false p) then
    fatal pos "The LHS is not typable.";
  let norm_constr (c,t,u) = (c, Eval.snf [] t, Eval.snf [] u) in
  let lhs_constrs = List.map norm_constr !p.unsolved in
  if Logger.log_enabled () then
    log_subj "@[<v>LHS type: %a@ LHS constraints: %a@ %a ↪ %a@]"
      term ty_lhs constrs lhs_constrs
      term lhs_with_metas term rhs_with_metas;
  (* We instantiate all the uninstantiated metavariables of the LHS (including
     those appearing in the types of these metavariables) using fresh function
     symbols. We also keep a list of those symbols. *)
  let symbols =
    let symbols = Stdlib.ref [] in
    let rec instantiate m =
      match !(m.meta_value) with
      | Some _ ->
        (* Instantiate recursively the meta-variables of the definition. *)
        let t = mk_Meta(m, Array.make m.meta_arity mk_Kind) in
        LibMeta.iter true instantiate [] t
      | None ->
        (* Instantiate recursively the meta-variables of the type. *)
        LibMeta.iter true instantiate [] !(m.meta_type);
        (* Instantiation of [m]. *)
        let s =
          let name = Pos.none @@ Printf.sprintf "$%d" m.meta_key in
          Term.create_sym (Sign.current_path()) Privat Defin Eager
            false name !(m.meta_type) [] in
        Stdlib.(symbols := s :: !symbols);
        (* Build a definition for [m]. *)
        let xs = Array.init m.meta_arity (new_tvar_ind "x") in
        let s = _Symb s in
        let def = Array.fold_left (fun t x -> _Appl t (_Vari x)) s xs in
        m.meta_value := Some(Bindlib.unbox (Bindlib.bind_mvar xs def))
    in
    Array.iter instantiate metas;
    Stdlib.(!symbols)
  in
  if Logger.log_enabled () then
    log_subj "replace LHS metavariables by function symbols:@ %a ↪ %a"
      term lhs_with_metas term rhs_with_metas;
  (* TODO complete the constraints into a set of rewriting rule on
     the function symbols of [symbols]. *)
  (* Compute the constraints for the RHS to have the same type as the LHS. *)
  let p = new_problem() in
  match Infer.check_noexn p [] rhs_with_metas ty_lhs with
  | None -> fatal pos "The RHS does not have the same type as the LHS."
  | Some rhs_with_metas ->
  (* Solving the typing constraints of the RHS. *)
  if not (Unif.solve_noexn p) then
    fatal pos "The rewriting rule does not preserve typing.";
  let rhs_constrs = List.map norm_constr !p.unsolved in
  (* [matches p t] says if [t] is an instance of [p]. *)
  let matches p t =
    let rec matches s l =
      match l with
      | [] -> ()
      | (p,t)::l ->
        (*if Logger.log_enabled() then
          log_subj "matches [%a] [%a]" term p term t;*)
        match unfold p, unfold t with
        | Vari x, _ ->
          begin match VarMap.find_opt x s with
            | Some u ->
              if Eval.eq_modulo [] t u then matches s l else raise Exit
            | None -> matches (VarMap.add x t s) l
          end
        | Symb f, Symb g when f == g -> matches s l
        | Appl(t1,u1), Appl(t2,u2) -> matches s ((t1,t2)::(u1,u2)::l)
        | _ -> raise Exit
    in try matches VarMap.empty [p,t]; true with Exit -> false
  in
  (* Function saying if a constraint is an instance of another one. *)
  let is_inst ((_c1,t1,u1) as x1) ((_c2,t2,u2) as x2) =
    if Logger.log_enabled() then
      log_subj "is_inst [%a] [%a]" constr x1 constr x2;
    let cons t u = add_args (mk_Symb Unif_rule.equiv) [t; u] in
    matches (cons t1 u1) (cons t2 u2) || matches (cons t1 u1) (cons u2 t2)
  in
  let is_lhs_constr rc = List.exists (fun lc -> is_inst lc rc) lhs_constrs in
  let cs = List.filter (fun rc -> not (is_lhs_constr rc)) rhs_constrs in
  if cs <> [] then
    begin
      List.iter (fatal_msg "Cannot solve %a@." constr) cs;
      fatal pos "Unable to prove type preservation."
    end;
  (* We build a map allowing to find a variable index from its key. *)
  let htbl : index_tbl = Hashtbl.create (Array.length vars) in
  Array.iteri
    (fun i m -> Hashtbl.add htbl (Printf.sprintf "$%d" m.meta_key) i)
    metas;
  (* Replace metavariable symbols by term_env variables, and bind them. *)
  let rhs = symb_to_tenv pr symbols htbl rhs_with_metas in
  (* TODO environment minimisation ? *)
  (* Construct the rule. *)
  let rhs = Bindlib.unbox (Bindlib.bind_mvar vars rhs) in
  { lhs ; rhs ; arity ; arities ; vars; xvars_nb = 0; rule_pos = pos }
