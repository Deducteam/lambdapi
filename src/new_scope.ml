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

(** Representation of the different scoping modes.  Note that the constructors
    hold specific information for the given mode. *)
type mode =
  | M_Term of meta StrMap.t ref
  (** Standard scoping mode for terms, holding a map of defined metavariables,
      and returning the updated map after scoping. *)
  | M_LHS  of int option StrMap.t
  (** Left-hand side mode, used for scoping patterns.  The constructor carries
      a map associating an optional index to every pattern variable. *)
  | M_RHS  of tevar StrMap.t
  (** Right-hand side mode. The constructor carries the environment for higher
      order variables that will be bound in the representation of the RHS. *)

let scope : mode -> sig_state -> env -> p_term -> term = fun md ss env t ->
  let rec scope : env -> p_term -> tbox = fun env t ->
    let scope_domain : env -> p_term option -> tbox = fun env t ->
      match t with
      | Some(t) -> scope env t
      | None    ->
          (* We build a metavariable that may use the variables of [env]. *)
          let a = prod_of_env env _Type in
          let vs = Env.vars_of_env env in
          _Meta (fresh_meta a (Array.length vs)) vs
    in
    match (t.elt, md) with
    | (P_Type          , M_LHS(_) ) -> fatal t.pos "Sort in LHS."
    | (P_Type          , _        ) -> _Type
    | (P_Vari(qid)     , _        ) -> find_qid ss env qid
    | (P_Wild          , _        ) -> _Wild
    | (P_Meta(id,ts)   , M_Term(m)) ->
        let v =
          (* We first check if the metavariable is in the map. *)
          try StrMap.find id.elt !m with Not_found ->
          (* Otherwise we create a new metavariable. *)
          let a =
            let vs = Env.vars_of_env env in
            let m = fresh_meta (prod_of_env env _Type) (Array.length vs) in
            prod_of_env env (_Meta m vs)
          in
          let v = fresh_meta ~name:id.elt a (List.length env) in
          m := StrMap.add id.elt v !m; v
        in
        (* The environment of the metavariable is build from [ts]. *)
        _Meta v (Array.map (scope env) ts)
    | (P_Meta(_,_)     , _        ) -> fatal t.pos "Metavariable in rule."
    | (P_Patt(_,_)     , M_Term(_)) -> fatal t.pos "Pattern variable in term."
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
    | (P_Appl(t,u)     , _        ) -> _Appl (scope env t) (scope env u)
    | (P_Impl(_,_)     , M_LHS(_) ) -> fatal t.pos "Implication in LHS."
    | (P_Impl(a,b)     , _        ) -> _Impl (scope env a) (scope env b)
    | (P_Abst(xs,t)    , _        ) ->
        let rec scope_abst env xs =
          match xs with
          | []        -> scope env t
          | (x,a)::xs ->
              let v = Bindlib.new_var mkfree x.elt in
              let a = scope_domain env a in
              let t = scope_abst (Env.add x.elt v a env) xs in
              _Abst a (Bindlib.bind_var v t)
        in
        scope_abst env xs
    | (P_Prod(xs,b)    , _        ) ->
        let rec scope_prod env xs =
          match xs with
          | []        -> scope env b
          | (x,a)::xs ->
              let v = Bindlib.new_var mkfree x.elt in
              let a = scope_domain env a in
              let b = scope_prod (Env.add x.elt v a env) xs in
              _Prod a (Bindlib.bind_var v b)
        in
        scope_prod env xs
    | (P_LLet(x,xs,t,u), _        ) ->
        (* “let x = t in u” is desugared as “(λx.u) t” (for now). *)
        let t = scope env (Pos.none (P_Abst(xs,t))) in
        _Appl (scope env (Pos.none (P_Abst([(x,None)], u)))) t
  in
  Bindlib.unbox (scope env t)
