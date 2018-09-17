(** Scoping. *)

open Timed
open Console
open Extra
open Files
open Pos
open Syntax
open Terms
open Env

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { in_scope : (sym * Pos.popt) StrMap.t (** Symbols in scope.    *)
  ; aliases  : module_path StrMap.t      (** Established aliases. *) }

(** [empty_sig_state] is an empty signature state, without symbols/aliases. *)
let empty_sig_state : sig_state =
  { in_scope = StrMap.empty ; aliases = StrMap.empty }

(** [find_qid st env qid] returns a boxed term corresponding to a variable  of
    the environment [env] (or to a symbol) which name corresponds to [qid]. In
    the case where the module path [fst qid.elt] is empty, we first search for
    the name [snd qid.elt] in the environment, and if it is not mapped we also
    search in the opened modules.  The exception [Fatal] is raised if an error
    occurs (e.g., when the name cannot be found). *)
let find_qid : sig_state -> env -> qident -> tbox = fun st env qid ->
  let {elt = (mp, s); pos} = qid in
  match mp with
  | []                               -> (** Variable or symbol in scope. *)
      begin
        (* Search the local environment first. *)
        try _Vari (Env.find s env) with Not_found ->
        (* Then, search symbols in scope. *)
        try _Symb (fst (StrMap.find s st.in_scope)) with Not_found ->
        fatal pos "Unbound variable or symbol [%s]." s
      end
  | [m] when StrMap.mem m st.aliases -> (** Aliased module path. *)
      begin
        (* The signature must be loaded (alias is mapped). *)
        let sign =
          try PathMap.find (StrMap.find m st.aliases) Timed.(!Sign.loaded)
          with _ -> assert false (* cannot fail. *)
        in
        (* Look for the symbol. *)
        try _Symb (Sign.find sign s) with Not_found ->
        fatal pos "Unbound symbol [%a.%s]." Files.pp_path mp s
      end
  | _                                -> (** Fully-qualified symbol. *)
      begin
        (* Check that the signature exists. *)
        let sign =
          try PathMap.find mp Timed.(!Sign.loaded) with Not_found ->
          fatal pos "No module [%a] loaded." Files.pp_path mp
        in
        (* Look for the symbol. *)
        try _Symb (Sign.find sign s) with Not_found ->
        fatal pos "Unbound symbol [%a.%s]." Files.pp_path mp s
      end

(** Map of metavariables. *)
type metamap = meta StrMap.t

(** Representation of the different scoping modes.  Note that the constructors
    hold specific information for the given mode. *)
type mode =
  | M_Term of metamap Pervasives.ref
  (** Standard scoping mode for terms,  holding a map of defined metavariables
      that can be updated with new metavariable on scoping. *)
  | M_Patt
  (** Scoping as a rewriting pattern. *)
  | M_LHS  of int option StrMap.t
  (** Left-hand side mode, used for scoping patterns.  The constructor carries
      a map associating an optional index to every pattern variable. *)
  | M_RHS  of tevar StrMap.t
  (** Right-hand side mode. The constructor carries the environment for higher
      order variables that will be bound in the representation of the RHS. *)

(** [scope md ss env t] turns a parser-level term [t] into an actual term. The
    variables of the environment [env] may appear in [t], and the scoping mode
    [md] changes the behaviour related to certain constructors.  The signature
    state [ss] is used to hande module aliasing according to [find_qid]. *)
let scope : mode -> sig_state -> env -> p_term -> term = fun md ss env t ->
  let rec scope : env -> p_term -> tbox = fun env t ->
    let scope_domain : popt -> env -> p_term option -> tbox = fun pos env a ->
      match (a, md) with
      | (Some(a), M_LHS(_)) -> fatal a.pos "Annotation not allowed in a LHS."
      | (None   , M_RHS(_)) -> fatal pos "Missing type annotation in a RHS."
      | (Some(a), _       ) -> scope env a
      | (None   , _       ) ->
          (* We build a metavariable that may use the variables of [env]. *)
          let vs = Env.vars_of_env env in
          _Meta (fresh_meta (prod_of_env env _Type) (Array.length vs)) vs
    in
    match (t.elt, md) with
    | (P_Type          , M_LHS(_) ) -> fatal t.pos "Not allowed in a LHS."
    | (P_Type          , _        ) -> _Type
    | (P_Vari(qid)     , _        ) -> find_qid ss env qid
    | (P_Wild          , _        ) -> _Wild
    | (P_Meta(id,ts)   , M_Term(m)) ->
        let v =
          (* We first check if the metavariable is in the map. *)
          try StrMap.find id.elt Pervasives.(!m) with Not_found ->
          (* Otherwise we create a new metavariable. *)
          let a =
            let vs = Env.vars_of_env env in
            let m = fresh_meta (prod_of_env env _Type) (Array.length vs) in
            prod_of_env env (_Meta m vs)
          in
          let v = fresh_meta ~name:id.elt a (List.length env) in
          Pervasives.(m := StrMap.add id.elt v !m); v
        in
        (* The environment of the metavariable is build from [ts]. *)
        _Meta v (Array.map (scope env) ts)
    | (P_Meta(_,_)     , _        ) -> fatal t.pos "Not allowed in a rule."
    | (P_Patt(id,ts)   , M_LHS(m) ) ->
        let i =
          try StrMap.find id.elt m with Not_found -> (* Should not happen. *)
          fatal t.pos "Pattern variable not in scope."
        in
        _Patt i id.elt (Array.map (scope env) ts)
    | (P_Patt(id,ts)   , M_RHS(m) ) ->
        let x =
          try StrMap.find id.elt m with Not_found -> (* Should not happen. *)
          fatal t.pos "Pattern variable not in scope."
        in
        _TEnv (Bindlib.box_var x) (Array.map (scope env) ts)
    | (P_Patt(_,_)     , _        ) -> fatal t.pos "Only allowed in rules."
    | (P_Appl(t,u)     , _        ) -> _Appl (scope env t) (scope env u)
    | (P_Impl(_,_)     , M_LHS(_) ) -> fatal t.pos "Not allowed in a LHS."
    | (P_Impl(_,_)     , M_Patt   ) -> fatal t.pos "Not allowed in a pattern."
    | (P_Impl(a,b)     , _        ) -> _Impl (scope env a) (scope env b)
    | (P_Abst(_,_)     , M_Patt   ) -> fatal t.pos "Not allowed in a pattern."
    | (P_Abst(xs,t)    , _        ) ->
        let rec scope_abst env xs =
          match xs with
          | []        -> scope env t
          | (x,a)::xs ->
              let v = Bindlib.new_var mkfree x.elt in
              let a = scope_domain x.pos env a in
              let t = scope_abst (Env.add x.elt v a env) xs in
              _Abst a (Bindlib.bind_var v t)
        in
        assert (xs <> []); scope_abst env xs
    | (P_Prod(_,_)     , M_LHS(_) ) -> fatal t.pos "Not allowed in a LHS."
    | (P_Prod(_,_)     , M_Patt   ) -> fatal t.pos "Not allowed in a pattern."
    | (P_Prod(xs,b)    , _        ) ->
        let rec scope_prod env xs =
          match xs with
          | []        -> scope env b
          | (x,a)::xs ->
              let v = Bindlib.new_var mkfree x.elt in
              let a = scope_domain x.pos env a in
              let b = scope_prod (Env.add x.elt v a env) xs in
              _Prod a (Bindlib.bind_var v b)
        in
        assert (xs <> []); scope_prod env xs
    | (P_LLet(x,xs,t,u), M_Term(_)) ->
        (* “let x = t in u” is desugared as “(λx.u) t” (for now). *)
        let t = scope env (Pos.none (P_Abst(xs,t))) in
        _Appl (scope env (Pos.none (P_Abst([(x,None)], u)))) t
    | (P_LLet(_,_,_,_) , _        ) -> fatal t.pos "Only allowed in terms."
  in
  Bindlib.unbox (scope env t)

(** [scope md ss env t] turns a parser-level term [t] into an actual term. The
    variables of the environment [env] may appear in [t], and the scoping mode
    [md] changes the behaviour related to certain constructors.  The signature
    state [ss] is used to hande module aliasing according to [find_qid]. *)
let scope_term : metamap -> sig_state -> env -> p_term
    -> term * metamap = fun m ss env t ->
  let m = Pervasives.ref m in
  let t = scope (M_Term(m)) ss env t in  
  (t, Pervasives.(!m))

(** [scope_rule ss r] turns a parser-level rewriting rule [r] into a rewriting
    rule (and the associated head symbol). *)
let scope_rule : sig_state -> p_rule -> sym * rule = fun ss (p_lhs, p_rhs) ->
  ignore (ss, p_lhs, p_rhs);
  assert false (* TODO *)

(** [scope_pattern ss env t] turns a parser-level term [t] into an actual term
    that will correspond to selection pattern (rewrite tactic). *)
let scope_pattern : sig_state -> env -> p_term -> term = scope M_Patt

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
let scope_rw_patt : sig_state ->  env -> p_rw_patt loc
    -> Rewrite.rw_patt = fun ss env s ->
  let open Rewrite in
  match s.elt with
  | P_rw_Term(t)               -> RW_Term(scope_pattern ss env t)
  | P_rw_InTerm(t)             -> RW_InTerm(scope_pattern ss env t)
  | P_rw_InIdInTerm(x,t)       ->
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind))::env) t in
      RW_InIdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_rw_IdInTerm(x,t)         ->
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind))::env) t in
      RW_IdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_rw_TermInIdInTerm(u,x,t) ->
      let u = scope_pattern ss env u in
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind))::env) t in
      RW_TermInIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_rw_TermAsIdInTerm(u,x,t) ->
      let u = scope_pattern ss env u in
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind))::env) t in
      RW_TermAsIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
