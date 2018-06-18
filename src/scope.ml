(** Scoping. *)

open Console
open Files
open Parser
open Terms
open Cmd
open Pos
open Extra
open Proofs

(** Extend an [env] with the mapping [(s,(v,a))] if s <> "_". *)
let add_env : string -> tvar -> tbox -> env -> env =
  fun s v a env -> if s = "_" then env else (s,(v,a))::env

(** [find_ident env qid] returns a bindbox corresponding to a variable of
    the environment [env], or to a symbol, which name corresponds to [qid]. In
    the case where the module path [fst qid.elt] is empty, we first search for
    the name [snd qid.elt] in the environment, and if it is not mapped we also
    search in the current signature. If the name does not correspond to
    anything, the program fails gracefully. *)
let find_ident : env -> qident -> tbox = fun env qid ->
  let {elt = (mp, s); pos} = qid in
  if mp = [] then
    (* No module path, search the local environment first. *)
    try _Vari (fst (List.assoc s env)) with Not_found ->
    (* Then, search in hypotheses. *)
    try _Vari (fst (List.assoc s (focus_goal_hyps()))) with Not_found ->
    (* Then, search in the global environment. *)
    try _Symb (Sign.find (Sign.current_sign()) s) with Not_found ->
    fatal pos "Unbound variable or symbol [%s]." s
  else
    let sign = Sign.current_sign() in
    if not Sign.(mp = sign.path || PathMap.mem mp !(sign.deps)) then
    (* Module path is not available (not loaded), fail. *)
    fatal pos "No module [%a] loaded." Files.pp_path mp
  else
    (* Module path loaded, look for symbol. *)
    let sign =
      try PathMap.find mp !Sign.loaded
      with _ -> assert false (* cannot fail. *)
    in
    try _Symb (Sign.find sign s) with Not_found ->
    fatal pos "Unbound symbol [%a.%s]." Files.pp_path mp s

(** [scope_meta_name loc id] translates the p_term-level metavariable
    name [id] into a term-level metavariable name. The position [loc] of
    [id] is used to build an error message in the case where [id] is
    invalid. *)
let scope_meta_name loc id =
  match id with
  | M_User(s)                                 -> User(s)
  | M_Sys(k)  when Metas.exists_meta (Sys(k)) -> Sys(k)
  | M_Sys(k)                                  ->
      fatal loc "Unknown metavariable [?%i]" k

(** Given an environment [x1:T1, .., xn:Tn] and a boxed term [t] with
    free variables in [x1, .., xn], build the product type [x1:T1 ->
    .. -> xn:Tn -> t]. *)
let prod_of_env : env -> tbox -> term = fun c t ->
  let prod b (_,(v,a)) = _Prod a v b in
  Bindlib.unbox (List.fold_left prod t c)

(** [prod_vars_of_env metas env is_type] builds the variables [vs] of
    [env] and the product [a] of [env] over [Type]. Then, it returns
    [a] if [is_type] is [true]. Otherwise, it adds [m] into [metas]
    and returns [m[vs]] where [m] is a new metavariable of arity the
    length of [env] and type [a]. Returns also [vs] in both cases. *)
let prod_vars_of_env : meta list ref -> env -> bool -> term * tbox array =
  fun metas env is_type ->
    let a = prod_of_env env _Type in
    let vs = Array.of_list (List.rev_map tvar_of_name env) in
    if is_type then (a, vs)
    else (* We create a new metavariable of type [a]. *)
      let m = Metas.add_sys_meta a (List.length env) in
      metas := m::!metas; (prod_of_env env (_Meta m vs), vs)

(** [meta_of_env metas env is_type] builds a new metavariable of type
    [prod_vars_of_env env is_type]. It adds new metavariables in
    [metas] too. *)
let meta_of_env : meta list ref -> env -> bool -> tbox =
  fun metas env is_type ->
    let t, vs = prod_vars_of_env metas env is_type in
    let m = Metas.add_sys_meta t (List.length env) in
    metas := m::!metas; _Meta m vs

(** [scope_term metas t] transforms a parser-level term [t] into an actual
    term and the list of the new metavariables that it contains. Note
    that wildcards [P_Wild] are transformed into fresh meta-variables.
    The same goes for the type carried by abstractions when it is not
    given. It adds new metavariables in [metas] too. *)
let scope_term : meta list ref -> p_term -> term = fun metas t ->
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> _Type
    | P_Prod(x,a,b) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env a in
        _Prod a v (scope (add_env x.elt v a env) b)
    | P_Abst(x,a,t) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env a in
        _Abst a v (scope (add_env x.elt v a env) t)
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        -> meta_of_env metas env false
    | P_Meta(id,ts) ->
        let id = scope_meta_name t.pos id in
        let m =
          try Metas.find_meta id with Not_found ->
            let s = match id with User(s) -> s | _ -> assert false in
            let (t,_) = prod_vars_of_env metas env false in
            let m = Metas.add_user_meta s t (List.length env) in
            metas := m :: !metas; m
        in
        _Meta m (Array.map (scope env) ts)
  and scope_domain : env -> p_term option -> tbox = fun env t ->
    match t with
    | Some(t) -> scope env t
    | None    -> meta_of_env metas env true
  in
  Bindlib.unbox (scope [] t)

(** Association list giving an environment index to “pattern variable”. *)
type meta_map = (string * int) list

(** Representation of a rule LHS (or pattern). It contains the head symbol and
    the list of arguments. *)
type full_lhs = sym * term list

(** [scope_lhs map t] computes a rule LHS from the parser-level term [t].  The
    association list [map] gives the index that is reserved in the environment
    for “pattern variables”.  Only the variables that are bound in the RHS (or
    appear non-linearly in the LHS) have an associated index in [map]. *)
let scope_lhs : meta_map -> p_term -> full_lhs = fun map t ->
  let fresh =
    let c = ref (-1) in
    fun () -> incr c; Printf.sprintf "#%i" !c
  in
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> fatal t.pos "Invalid LHS (sort [Type])."
    | P_Prod(_,_,_) -> fatal t.pos "Invalid LHS (product type)."
    | P_Abst(x,a,t) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env a in
        _Abst a v (scope (add_env x.elt v a env) t)
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        ->
        let e = List.map tvar_of_name env in
        let m = fresh () in
        _Patt None m (Array.of_list e)
    | P_Meta(m,ts)  ->
        let e = Array.map (scope env) ts in
        let s =
          match m with
          | M_User(s) -> s
          | _         -> fatal t.pos "Invalid LHS (system metavariable)."
        in
        let i = try Some(List.assoc s map) with Not_found -> None in
        _Patt i s e
  and scope_domain : env -> p_term option -> tbox = fun env t ->
    match t with
    | Some(t) -> fatal t.pos "Invalid LHS (type annotation)."
    | None    -> scope env (Pos.none P_Wild)
  in
  match get_args (Bindlib.unbox (scope [] t)) with
  | (Symb(s), _ ) when s.sym_const ->
      fatal t.pos "LHS with a static head symbol."
  | (Symb(s), ts) -> (s, ts)
  | (_      , _ ) ->
      fatal t.pos "LHS with no head symbol." Pos.print t.pos

(* NOTE wildcards are given a unique name so that we can produce more readable
   error messages. The names are formed of a number prefixed by ['#']. *)

(** Representation of the RHS of a rule. *)
type rhs = (term_env, term) Bindlib.mbinder

(** [scope_rhs map t] computes a rule RHS from the parser-level term [t].
    The association list [map] gives the position of
    every “pattern variable” in the constructed multiple binder. *)
let scope_rhs : meta_map -> p_term -> rhs = fun map t ->
  let names =
    let sorted_map = List.sort (fun (_,i) (_,j) -> i - j) map in
    Array.of_list (List.map fst sorted_map)
  in
  let metas = Bindlib.new_mvar (fun m -> TE_Vari(m)) names in
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> _Type
    | P_Prod(x,a,b) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env t.pos a in
        _Prod a v (scope (add_env x.elt v a env) b)
    | P_Abst(x,a,t) ->
        let v = Bindlib.new_var mkfree x.elt in
        let a = scope_domain env t.pos a in
        _Abst a v (scope (add_env x.elt v a env) t)
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        -> fatal t.pos "Invalid RHS (wildcard).\n"
    | P_Meta(m,e)   ->
        let e = Array.map (scope env) e in
        let m =
          match m with
          | M_User(s) -> s
          | _         -> fatal t.pos "Invalid RHS (system metavariable)."
        in
        try
          let i = List.assoc m map in
          _TEnv (Bindlib.box_var metas.(i)) e
        with Not_found ->
          fatal t.pos "Unbound pattern variable [%s]." m
  and scope_domain : env -> popt -> p_term option -> tbox = fun env p t ->
    match t with
    | Some(t) -> scope env t
    | None    -> fatal p "Missing type annotation."
  in
  Bindlib.unbox (Bindlib.bind_mvar metas (scope [] t))

(** [meta_vars t] returns a couple [(mvs,nl)]. The first compoment [mvs] is an
    association list giving the arity of all the “pattern variables” appearing
    in the parser-level term [t]. The second component [nl] contains the names
    of the “pattern variables” that appear non-linearly.  If a given  “pattern
    variable” occurs with different arities the program fails gracefully. *)
let meta_vars : p_term -> (string * int) list * string list = fun t ->
  let rec meta_vars acc t =
    match t.elt with
    | P_Vari(_)
    | P_Type
    | P_Wild              -> acc
    | P_Prod(_,None,b)
    | P_Abst(_,None,b)    -> meta_vars acc b
    | P_Prod(_,Some(a),b)
    | P_Abst(_,Some(a),b)
    | P_Appl(a,b)         -> meta_vars (meta_vars acc a) b
    | P_Meta(M_User(m),e) ->
        let ((ar,nl) as acc) = Array.fold_left meta_vars acc e in
        if m = "_" then acc else
        let l = Array.length e in
        begin
          try
            if List.assoc m ar <> l then
              fatal t.pos "Arity mismatch for metavariable [%s]." m;
            if List.mem m nl then acc else (ar, m::nl)
          with Not_found -> ((m,l)::ar, nl)
        end
    | P_Meta(_,_)         -> fatal t.pos "Invalid rule member."
  in meta_vars ([],[]) t

(** [scope_rule r] scopes a parsing level reduction rule, producing every
    element that is necessary to check its type and print error messages. This
    includes the context the symbol, the LHS / RHS as terms and the rule. *)
let scope_rule : p_rule -> sym * rule = fun (p_lhs, p_rhs) ->
  (* Compute the set of the meta-variables on both sides. *)
  let (mvs_lhs, nl) = meta_vars p_lhs in
  let (mvs    , _ ) = meta_vars p_rhs in
  (* NOTE: to reject non-left-linear rules, we can check [nl = []] here. *)
  (* Check that the meta-variables of the RHS exist in the LHS. *)
  let check_in_lhs (m,i) =
    let j =
      try List.assoc m mvs_lhs with Not_found ->
      fatal p_rhs.pos "Unknown pattern variable [%s]." m
    in
    if i <> j then fatal p_lhs.pos "Arity mismatch for [%s]." m
  in
  List.iter check_in_lhs mvs;
  let mvs = List.map fst mvs in
  (* Reserve space for meta-variables that appear non-linearly in the LHS. *)
  let nl = List.filter (fun m -> not (List.mem m mvs)) nl in
  let mvs = List.mapi (fun i m -> (m,i)) (mvs @ nl) in
  (* NOTE: [mvs] maps meta-variables to their position in the environment. *)
  (* NOTE: meta-variables not in [mvs] can be considered as wildcards. *)
  (* We scope the LHS and add indexes in the enviroment for meta-variables. *)
  let (sym, lhs) = scope_lhs mvs p_lhs in
  (* We scope the RHS and bind the meta-variables. *)
  let rhs = scope_rhs mvs p_rhs in
  (* We put everything together to build the rule. *)
  (sym, {lhs; rhs; arity = List.length lhs})

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun (ctx,lhs,rhs) ->
  let ctx = List.map (fun (x,_) -> x.elt) ctx in
  let is_pat_var env x = not (List.mem x env) && List.mem x ctx in
  let arity = Hashtbl.create 7 in
  let rec build env t =
    let h, lts = Parser.get_args t in
    match h.elt with
    | P_Vari({elt = ([],x)}) when is_pat_var env x ->
       let lts = List.map (fun (p,t) -> p,build env t) lts in
       begin
         try
           let n = Hashtbl.find arity x in
           let lts1, lts2 = List.cut lts n in
           let ts1 = List.map snd lts1 in
           let h = Pos.make t.pos (P_Meta(M_User(x),Array.of_list ts1)) in
           Parser.add_args h lts2
         with Not_found ->
           Hashtbl.add arity x (List.length lts);
           let ts = List.map snd lts in
           Pos.make t.pos (P_Meta(M_User(x),Array.of_list ts))
       end
    | _ ->
       match t.elt with
       | P_Vari(_)
       | P_Type
       | P_Wild -> t
       | P_Prod(_,None,_) -> assert false
       | P_Prod(x,Some(a),b) ->
          let a = build env a in
          let b = build (x.elt::env) b in
          Pos.make t.pos (P_Prod(x,Some(a),b))
       | P_Abst(x,a,u) ->
          let a = match a with Some(a) -> Some(build env a) | _ -> None in
          let u = build (x.elt::env) u in
          Pos.make t.pos (P_Abst(x,a,u))
       | P_Appl(t1,t2) ->
          let t1 = build env t1 in
          let t2 = build env t2 in
          Pos.make t.pos (P_Appl(t1,t2))
       | P_Meta(_,_)   ->
          fatal t.pos "Invalid legacy rule syntax."
  in
  let l = build [] lhs in
  let r = build [] rhs in
  (* the order is important for setting arities properly *)
  (l,r)

(** [scope_cmd_aux cmd] scopes the parser level command [cmd].
    In case of error, the program gracefully fails. *)
let scope_cmd_aux : meta list ref -> p_cmd -> cmd_aux = fun metas cmd ->
  match cmd with
  | P_SymDecl(b,x,a)  -> SymDecl(b, x, scope_term metas a)
  | P_SymDef(b,x,ao,t) ->
      let t = scope_term metas t in
      let ao =
        match ao with
        | None    -> None
        | Some(a) -> Some(scope_term metas a)
      in
      SymDef(b,x,ao,t)
  | P_Rules(rs)         -> Rules(List.map scope_rule rs)
  | P_OldRules(rs)      ->
      let rs = List.map translate_old_rule rs in
      Rules(List.map scope_rule rs)
  | P_Require(path)     -> Require(path)
  | P_Debug(b,s)        -> Debug(b,s)
  | P_Verb(n)           -> Verb(n)
  | P_Infer(t,c)        -> Infer(scope_term metas t, c)
  | P_Eval(t,c)         -> Eval(scope_term metas t, c)
  | P_TestType(ia,mf,t,a) ->
      let test_type = HasType(scope_term metas t, scope_term metas a) in
      Test({is_assert = ia; must_fail = mf; test_type})
  | P_TestConv(ia,mf,t,u) ->
      let test_type = Convert(scope_term metas t, scope_term metas u) in
      Test({is_assert = ia; must_fail = mf; test_type})
  | P_Other(c)          -> Other(c)
  | P_StartProof(s,a)   -> StartProof(s, scope_term metas a)
  | P_PrintFocus        -> PrintFocus
  | P_Refine(t)         -> Refine (scope_term metas t)
  | P_Simpl             -> Simpl

(** [scope_cmd_aux cmd] scopes the parser level command [cmd],
    and forwards the source code position of the command. In
    case of error, the program gracefully fails. *)
let scope_cmd : p_cmd loc -> cmd * meta list = fun cmd ->
  let metas = ref [] in
  let cmd_aux = scope_cmd_aux metas cmd.elt in
  {elt = cmd_aux; pos = cmd.pos}, !metas
