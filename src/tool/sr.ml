(** Type-checking and inference. *)

open! Lplib
open Timed
open Common
open Error
open Core
open Parsing
open Term
open Print
open Debug
open Extra

(** Logging function for typing. *)
let log_subj = new_logger 's' "subj" "subject-reduction"
let log_subj = log_subj.logger

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
let patt_to_tenv : term_env Bindlib.var array -> term -> tbox = fun vars ->
  let get_te i =
    match i with
    | None    -> assert false (* Cannot appear in LHS. *)
    | Some(i) -> try vars.(i) with Invalid_argument(_) -> assert false
  in
  let rec trans t =
    match unfold t with
    | Vari(x)     -> _Vari x
    | Symb(s)     -> _Symb s
    | Abst(a,b)   -> let (x, t) = Bindlib.unbind b in
                     _Abst (trans a) (Bindlib.bind_var x (trans t))
    | Appl(t,u)   -> _Appl (trans t) (trans u)
    | Patt(i,_,a) -> _TEnv (Bindlib.box_var (get_te i)) (Array.map trans a)
    | Type        -> assert false (* Cannot appear in LHS. *)
    | Kind        -> assert false (* Cannot appear in LHS. *)
    | Prod(_,_)   -> assert false (* Cannot appear in LHS. *)
    | LLet(_,_,_) -> assert false (* Cannot appear in LHS. *)
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
      | Symb(f) when List.memq f syms ->
          let i =
            try Hashtbl.find htbl f.sym_name with Not_found ->
            (* A symbol may also come from a metavariable that appeared in the
               type of a metavariable that was replaced by a symbol. We do not
               have concrete examples of that happening yet. *)
            fatal pos "Introduced symbol [%s] cannot be removed." f.sym_name
          in
          let (ts1, ts2) = List.cut ts arities.(i) in
          (_TEnv (Bindlib.box_var vars.(i)) (Array.of_list ts1), ts2)
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
     fatal pos "Unknown pattern variables: %a"
       (Array.pp Print.pp_var ",") xvars);
  let arity = List.length lhs in
  if !log_enabled then
    begin
      (* The unboxing here could be harmful since it leads to [pr_rhs] being
         unboxed twice. However things should be fine here since the result is
         only used for printing. *)
      let rhs = Bindlib.(unbox (bind_mvar vars pr_rhs)) in
      let naive_rule = {lhs; rhs; arity; arities; vars; xvars_nb = 0} in
      log_subj (red "%a") pp_rule (s, naive_rule);
    end;
  (* Replace [Patt] nodes of LHS with corresponding elements of [vars]. *)
  let lhs_vars = _Appl_Symb s (List.map (patt_to_tenv vars) lhs) in
  (* Create metavariables that will stand for the variables of [vars].
     These metavariables are prefixed by "$" so that we can recognize them. *)
  let var_names = Array.map (fun x -> "$" ^ Bindlib.name_of x) vars in
  let p = new_problem() in
  let metas =
    let f i name =
      let arity = arities.(i) in
      LibMeta.fresh p ~name (build_meta_type p arity) arity
    in Array.mapi f var_names
  in
  (* Substitute them in the LHS and in the RHS. *)
  let lhs_with_metas, rhs_with_metas =
    let lhs_rhs = Bindlib.box_pair lhs_vars pr_rhs in
    let b = Bindlib.(unbox (bind_mvar vars lhs_rhs)) in
    let meta_to_tenv m =
      let xs = Array.init m.meta_arity (new_tvar_ind "x") in
      let ts = Array.map _Vari xs in
      TE_Some(Bindlib.unbox (Bindlib.bind_mvar xs (_Meta m ts)))
    in
    let te_envs = Array.map meta_to_tenv metas in
    Bindlib.msubst b te_envs
  in
  if !log_enabled then
    log_subj "replace pattern variables by metavariables\n%a ↪ %a"
      pp_term lhs_with_metas pp_term rhs_with_metas;
  (* Infer the typing constraints of the LHS. *)
  match Infer.infer_noexn p [] lhs_with_metas with
  | None -> fatal pos "The LHS is not typable."
  | Some ty_lhs ->
  (* Try to simplify constraints. Don't check typing when instantiating
     a metavariable. *)
  if not (Unif.solve_noexn ~type_check:false p) then
    fatal pos "The LHS is not typable.";
  let lhs_constrs = p.unsolved in
  if !log_enabled then
    log_subj "LHS: %a%a\n%a ↪ %a"
      pp_term ty_lhs pp_constrs lhs_constrs
      pp_term lhs_with_metas pp_term rhs_with_metas;
  (* We build a map allowing to find a variable index from its name. *)
  let htbl : index_tbl = Hashtbl.create (Array.length vars) in
  Array.iteri (fun i name -> Hashtbl.add htbl name i) var_names;
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
          LibMeta.iter true instantiate t
      | None ->
          (* Instantiate recursively the meta-variables of the type. *)
          LibMeta.iter true instantiate !(m.meta_type);
          (* Instantiation of [m]. *)
          let s = Term.create_sym (Sign.current_path()) Privat Defin Eager
                    false (LibMeta.name m) !(m.meta_type) [] in
          Stdlib.(symbols := s :: !symbols);
          (* Build a definition for [m]. *)
          let xs = Array.init m.meta_arity (new_tvar_ind "x") in
          let s = _Symb s in
          let def = Array.fold_left (fun t x -> _Appl t (_Vari x)) s xs in
          m.meta_value := Some(Bindlib.unbox (Bindlib.bind_mvar xs def))
    in
    Array.iter instantiate metas; Stdlib.(!symbols)
  in
  if !log_enabled then
    log_subj "replace LHS metavariables by function symbols\n%a ↪ %a"
      pp_term lhs_with_metas pp_term rhs_with_metas;
  (* TODO complete the constraints into a set of rewriting rule on
     the function symbols of [symbols]. *)
  (* Compute the constraints for the RHS to have the same type as the LHS. *)
  let p = new_problem() in
  if not (Infer.check_noexn p [] rhs_with_metas ty_lhs) then
    fatal pos "The RHS does not have the same type as the LHS.";
  (* Solving the typing constraints of the RHS. *)
  if not (Unif.solve_noexn p) then
    fatal pos "The rewriting rule does not preserve typing.";
  let is_lhs_constr c =
    (* Contexts ignored: [Infer.check] is called with an empty context and
       neither [Infer.check] nor [Unif.solve] generate contexts with defined
       variables. *)
    let eq (_,t1,u1) (_,t2,u2) =
      Eval.(eq_modulo [] t1 t2 && eq_modulo [] u1 u2)
      || Eval.(eq_modulo [] t1 u2 && eq_modulo [] t2 u1) in
    List.exists (eq c) lhs_constrs
  in
  let cs = List.filter (fun c -> not (is_lhs_constr c)) p.unsolved in
  if cs <> [] then
    begin
      List.iter (fatal_msg "Cannot solve %a\n" pp_constr) cs;
      fatal pos "Unable to prove type preservation for a rewriting rule."
    end;
  (* Replace metavariable symbols by term_env variables, and bind them. *)
  let rhs = symb_to_tenv pr symbols htbl rhs_with_metas in
  (* TODO environment minimisation ? *)
  (* Construct the rule. *)
  let rhs = Bindlib.unbox (Bindlib.bind_mvar vars rhs) in
  { lhs ; rhs ; arity ; arities ; vars; xvars_nb = 0 }
