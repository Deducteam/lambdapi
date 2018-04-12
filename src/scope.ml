(** Scoping. *)

open Console
open Files
open Terms
open Parser
open Cmd
open Pos

(** Flag to enable a warning if an abstraction is not annotated (with the type
    of its domain). *)
let wrn_no_type : bool ref = ref false

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
  let (mp, s) = qid.elt in
  if mp = [] then
    (* No module path, search the local environment first. *)
    try _Vari (fst (List.assoc s env))
    with Not_found ->
      (* Then, search in hypotheses. *)
      try _Vari (fst (List.assoc s (Sign.focus_goal_hyps())))
      with Not_found ->
        (* Then, search in the global environment. *)
        try _Symb (Sign.find (Sign.current_sign()) s)
        with Not_found -> fatal "Unbound variable or symbol %S...\n%!" s
  else
    let sign = Sign.current_sign() in
    if not Sign.(mp = sign.path || PathMap.mem mp !(sign.deps)) then
    (* Module path is not available (not loaded), fail. *)
    let cur = String.concat "." Sign.(sign.path) in
    let req = String.concat "." mp in
    fatal "No module %s loaded in %s...\n%!" req cur
  else
    (* Module path loaded, look for symbol. *)
    let sign =
      try PathMap.find mp !Sign.(!current_state.s_loaded)
      with _ -> assert false (* cannot fail. *)
    in
    try _Symb (Sign.find sign s) with Not_found ->
    fatal "Unbound symbol %S...\n%!" (String.concat "." (mp @ [s]))

(** Given a boxed context [x1:T1, .., xn:Tn] and a boxed term [t] with
    free variables in [x1, .., xn], build the product type [x1:T1 ->
    .. -> xn:Tn -> t]. *)
let build_prod : env -> tbox -> term = fun c t ->
  let fn b (_,(v,a)) =
    Bindlib.box_apply2 (fun a f -> Prod(a,f)) a (Bindlib.bind_var v b)
  in Bindlib.unbox (List.fold_left fn t c)

(** [build_type is_type env] builds the product of [env] over [a] where
    [a] is [Type] if [is_type], and a new metavariable
    otherwise. Returns the array of variables of [env] too. *)
let build_meta_type : env -> bool -> term * tbox array =
  fun env is_type ->
    let a = build_prod env _Type in
    let fn (_,(v,_)) = Bindlib.box_of_var v in
    let vs = Array.of_list (List.rev_map fn env) in
    if is_type then a, vs
    else (* We create a new metavariable. *)
      let m = new_meta a (List.length env) in
      build_prod env (_Meta m vs), vs

(** [build_meta_app is_type c] builds a new metavariable of type
    [build_meta_type is_type c]. *)
let build_meta_app : env -> bool -> tbox =
  fun env is_type ->
    let t, vs = build_meta_type env is_type in
    let m = new_meta t (List.length env) in
    _Meta m vs

(** [build_meta_name loc id] builds a meta-variable name from its parser-level
    representation [id]. The position [loc] of [id] is used to build an  error
    message in the case where [id] is invalid. *)
let build_meta_name loc id =
  match id with
  | M_Bad(k)  -> fatal "Unknown metavariable [?%i] %a" k Pos.print loc
  | M_Sys(k)  -> Internal(k)
  | M_User(s) -> Defined(s)

(** [scope_term t] transforms a parser-level term [t] into an actual term
    (using Bindlib). Note that wildcards [P_Wild] are
    transformed into fresh meta-variables.  The same goes for the type carried
    by abstractions when it is not given. *)
let scope_term : p_term -> term = fun t ->
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> _Type
    | P_Prod(x,a,b) ->
        let a =
          match a with
          | Some(a) -> scope env a
          | None    -> build_meta_app env true
        in
        _Prod a x.elt (fun v -> scope (add_env x.elt v a env) b)
    | P_Abst(x,a,t) ->
        let a =
          match a with
          | Some(a) -> scope env a
          | None    -> build_meta_app env true
        in
        _Abst a x.elt (fun v -> scope (add_env x.elt v a env) t)
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        -> build_meta_app env false
    | P_Meta(id,ts) ->
        let id = build_meta_name t.pos id in
        let m =
          try find_meta id with Not_found ->
            let s = match id with Defined(s) -> s | _ -> assert false in
            let (t,_) = build_meta_type env false in
            add_meta s t (List.length env)
        in
        _Meta m (Array.map (scope env) ts)
  in
  Bindlib.unbox (scope [] t)

(** Association list giving an environment index to “pattern variable”. *)
type meta_map = (string * int) list

(** Representation of a rule LHS (or pattern). It contains the head symbol and
    the list of arguments (first two elements).  The last component associates
    a type to each “pattern variable” in the arguments. *)
type full_lhs = symbol * term list * (string * term) list

(** [scope_lhs map t] computes a rule LHS from the parser-level term [t].
    The association list [map] gives the position of
    every “pattern variable” in the environment.  Note that only the variables
    that are bound in the RHS (or that occur non-linearly in the LHS) have  an
    associated index in [map]. *)
let scope_lhs : meta_map -> p_term -> full_lhs = fun map t ->
  let fresh =
    let c = ref (-1) in
    fun () -> incr c; Printf.sprintf "#%i" !c
  in
  let ty_map = ref [] in (* stores the type of each pattern variable. *)
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Vari(qid)   -> find_ident env qid
    | P_Type        -> fatal "invalid pattern %a\n" Pos.print t.pos
    | P_Prod(_,_,_) -> fatal "invalid pattern %a\n" Pos.print t.pos
    | P_Abst(x,a,t) ->
        let a =
          match a with
          | Some(a) -> fatal "type in LHS %a" Pos.print a.pos
          | None    -> build_meta_app env true
        in
        _Abst a x.elt (fun v -> scope (add_env x.elt v a env) t)
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        ->
        let e = List.map (fun (_,(x,_)) -> Bindlib.box_of_var x) env in
        let m = fresh () in
        let (a,_) = build_meta_type env false in
        ty_map := (m, a) :: !ty_map;
        _Patt None m (Array.of_list e)
    | P_Meta(m,ts)  ->
        let e = Array.map (scope env) ts in
        let m =
          match m with
          | M_User(s) -> s
          | _         -> fatal "invalid pattern %a\n" Pos.print t.pos
        in
        let i = try Some(List.assoc m map) with Not_found -> None in
        let (a,_) =
          let fn (x,_) =
            let gn t =
              match t.elt with
              | P_Vari({elt = ([], y)}) -> x = y
              | _                       -> false
            in
            Array.exists gn ts
          in
          build_meta_type (List.filter fn env) false
        in
        ty_map := (m, a) :: !ty_map;
        _Patt i m e
  in
  match get_args (Bindlib.unbox (scope [] t)) with
  | (Symb(s), ts) ->
     if s.sym_definable then (s, ts, !ty_map)
     else fatal "%s is not a definable symbol...\n" s.sym_name
  | (_           , _ ) -> fatal "invalid pattern %a\n" Pos.print t.pos

(* NOTE wildcards are given a unique name so that we can produce more readable
   outputs. Their name is forme of a ['#'] character followed by a number. *)

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
    | P_Prod(_,None,_) -> fatal "missing type %a" Pos.print t.pos
    | P_Prod(x,Some(a),b) ->
        let a = scope env a in
        _Prod a x.elt (fun v -> scope (add_env x.elt v a env) b)
    | P_Abst(x,a,t) ->
        let a =
          match a with
          | Some(a) -> scope env a
          | None    -> build_meta_app env true
        in
        _Abst a x.elt (fun v -> scope (add_env x.elt v a env) t)
    | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
    | P_Wild        -> fatal "wildcard in RHS %a" Pos.print t.pos
    | P_Meta(m,e)   ->
        let e = Array.map (scope env) e in
        let m =
          match m with
          | M_User(s) -> s
          | _         -> fatal "invalid action %a\n" Pos.print t.pos
        in
        let i = try List.assoc m map with Not_found -> assert false in
        _TEnv (Bindlib.box_of_var metas.(i)) e
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
              fatal "arity mismatch for the meta variable %S...\n" m;
            if List.mem m nl then acc else (ar, m::nl)
          with Not_found -> ((m,l)::ar, nl)
        end
    | P_Meta(_,_)         ->
        fatal "invalid rule member %a" Pos.print t.pos
  in meta_vars ([],[]) t

(** [scope_rule r] scopes a parsing level reduction rule, producing every
    element that is necessary to check its type and print error messages. This
    includes the context the symbol, the LHS / RHS as terms and the rule. *)
let scope_rule : p_rule -> rspec = fun (p_lhs, p_rhs) ->
  (* Compute the set of the meta-variables on both sides. *)
  let (mvs_lhs, nl) = meta_vars p_lhs in
  let (mvs    , _ ) = meta_vars p_rhs in
  (* NOTE: to reject non-left-linear rules, we can check [nl = []] here. *)
  (* Check that the meta-variables of the RHS exist in the LHS. *)
  let check_in_lhs (m,i) =
    let j =
      try List.assoc m mvs_lhs with Not_found ->
      fatal "unknown pattern variable %S...\n" m
    in
    if i <> j then fatal "arity mismatch for pattern variable %S...\n" m
  in
  List.iter check_in_lhs mvs;
  let mvs = List.map fst mvs in
  (* Reserve space for meta-variables that appear non-linearly in the LHS. *)
  let nl = List.filter (fun m -> not (List.mem m mvs)) nl in
  let mvs = List.mapi (fun i m -> (m,i)) (mvs @ nl) in
  (* NOTE: [mvs] maps meta-variables to their position in the environment. *)
  (* NOTE: meta-variables not in [mvs] can be considered as wildcards. *)
  (* We scope the LHS and add indexes in the enviroment for meta-variables. *)
  let (sym, lhs, ty_map) = scope_lhs mvs p_lhs in
  (* We scope the RHS and bind the meta-variables. *)
  let rhs = scope_rhs mvs p_rhs in
  (* We put everything together to build the rule. *)
  let rule = {lhs; rhs; arity = List.length lhs} in
  {rspec_symbol = sym; rspec_ty_map = ty_map; rspec_rule = rule}

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun (ctx,lhs,rhs) ->
  let ctx = List.map (fun (x,_) -> x.elt) ctx in
  let rec build_lhs env t =
    match t.elt with
    | P_Vari(qid)   ->
        let (mp,x) = qid.elt in
        if mp = [] && not (List.mem x env) && List.mem x ctx then
          Pos.make t.pos (P_Meta(M_User(x),[||]))
          (* FIXME need more for Miller patterns. *)
        else Pos.make t.pos (P_Vari(qid))
    | P_Type        -> fatal "invalid legacy pattern %a\n" Pos.print t.pos
    | P_Prod(_,_,_) -> fatal "invalid legacy pattern %a\n" Pos.print t.pos
    | P_Abst(x,a,u) ->
        if a <> None then fatal "type in legacy pattern %a\n" Pos.print t.pos;
        let u = build_lhs (x.elt::env) u in
        Pos.make t.pos (P_Abst(x,a,u))
    | P_Appl(t1,t2) ->
        let t1 = build_lhs env t1 in
        let t2 = build_lhs env t2 in
        Pos.make t.pos (P_Appl(t1,t2))
    | P_Wild        -> t
    | P_Meta(_,_)   ->
        fatal "invalid legacy rule syntax %a\n" Pos.print t.pos
  in
  let rec build_rhs env t =
    match t.elt with
    | P_Vari(qid)   ->
        let (mp,x) = qid.elt in
        if mp = [] && not (List.mem x env) && List.mem x ctx then
          Pos.make t.pos (P_Meta(M_User(x),[||]))
          (* FIXME need more for Miller patterns. *)
        else Pos.make t.pos (P_Vari(qid))
    | P_Type        -> t
    | P_Prod(_,None,_) -> assert false
    | P_Prod(x,Some(a),b) ->
        let a = build_rhs env a in
        let b = build_rhs (x.elt::env) b in
        Pos.make t.pos (P_Prod(x,Some(a),b))
    | P_Abst(x,a,u) ->
        let a = match a with Some(a) -> Some(build_rhs env a) | _ -> None in
        let u = build_rhs (x.elt::env) u in
        Pos.make t.pos (P_Abst(x,a,u))
    | P_Appl(t1,t2) ->
        let t1 = build_rhs env t1 in
        let t2 = build_rhs env t2 in
        Pos.make t.pos (P_Appl(t1,t2))
    | P_Wild        ->
        fatal "invalid legacy rule syntax %a\n" Pos.print t.pos
    | P_Meta(_,_)   ->
        fatal "invalid legacy rule syntax %a\n" Pos.print t.pos
  in
  (build_lhs [] lhs, build_rhs [] rhs)

(** [scope_cmd_aux cmd] scopes the parser level command [cmd].
    In case of error, the program gracefully fails. *)
let scope_cmd_aux : p_cmd -> cmd_aux = fun cmd ->
  match cmd with
  | P_SymDecl(b,x,a)  -> SymDecl(b, x, scope_term a)
  | P_SymDef(b,x,ao,t) ->
      let t = scope_term t in
      let ao =
        match ao with
        | None    -> None
        | Some(a) -> Some(scope_term a)
      in
      SymDef(b,x,ao,t)
  | P_Rules(rs)         -> Rules(List.map scope_rule rs)
  | P_OldRules(rs)      ->
      let rs = List.map translate_old_rule rs in
      Rules(List.map scope_rule rs)
  | P_Require(path)     -> Require(path)
  | P_Debug(b,s)        -> Debug(b,s)
  | P_Verb(n)           -> Verb(n)
  | P_Infer(t,c)        -> Infer(scope_term t, c)
  | P_Eval(t,c)         -> Eval(scope_term t, c)
  | P_TestType(ia,mf,t,a) ->
      let test_type = HasType(scope_term t, scope_term a) in
      Test({is_assert = ia; must_fail = mf; test_type})
  | P_TestConv(ia,mf,t,u) ->
      let test_type = Convert(scope_term t, scope_term u) in
      Test({is_assert = ia; must_fail = mf; test_type})
  | P_Other(c)          -> Other(c)
  | P_StartProof(s,a)   -> StartProof(s, scope_term a)
  | P_PrintFocus        -> PrintFocus
  | P_Refine(t)         -> Refine (scope_term t)

(** [scope_cmd_aux cmd] scopes the parser level command [cmd],
    and forwards the source code position of the command. In
    case of error, the program gracefully fails. *)
let scope_cmd : p_cmd loc -> cmd = fun cmd ->
  {elt = scope_cmd_aux cmd.elt; pos = cmd.pos}
