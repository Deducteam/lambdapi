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
type mod_state =
  { in_scope : (sym * Pos.popt) StrMap.t (** Symbols in scope.    *)
  ; aliases  : module_path StrMap.t      (** Established aliases. *) }

(** [find_qid st env qid] returns a boxed term corresponding to a variable  of
    the environment [env] (or to a symbol) which name corresponds to [qid]. In
    the case where the module path [fst qid.elt] is empty, we first search for
    the name [snd qid.elt] in the environment, and if it is not mapped we also
    search in the opened modules.  The exception [Fatal] is raised if an error
    occurs (e.g., when the name cannot be found). *)
let find_qid : mod_state -> env -> qident -> tbox = fun st env qid ->
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
    hold specific information for the given mode. The type parameter gives the
    return type that is desired for the scoping function. *)
type 'a scoping_mode =
  | SM_Term : meta StrMap.t       -> (term * meta StrMap.t) scoping_mode
  (** Standard scoping mode for terms, holding a map of defined metavariables,
      and returning the updated map after scoping. *)
  | SM_LHS  : int option StrMap.t ->                   term scoping_mode
  (** Left-hand side mode, used for scoping patterns.  The constructor carries
      a map associating an optional index to every pattern variable. *)
  | SM_RHS  : tebox StrMap.t      ->                   term scoping_mode
  (** Right-hand side mode. The constructor carries the environment for higher
      order variables that will be bound in the representation of the RHS. *)

let scope_term : mod_state -> env -> p_term -> term = fun st env t ->
  let rec scope : env -> p_term -> tbox = fun env t ->
    match t.elt with
    | P_Type           -> _Type
    | P_Vari(qid)      -> find_qid st env qid
    | P_Wild           -> _Wild
    | P_Meta(m,ts)     ->
        assert false (* TODO *)
    | P_Patt(p,ts)     ->
        assert false (* TODO *)
    | P_Appl(t,u)      -> _Appl (scope env t) (scope env u)
    | P_Impl(a,b)      ->
        scope env (Pos.make t.pos (P_Prod([(Pos.none "_", Some(a))], b)))
    | P_Abst(xs,t)     ->
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
    | P_Prod(xs,b)     ->
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
    | P_LLet(x,xs,t,u) ->
        (* “let x = t in u” is desugared as “(λx.u) t” (for now). *)
        let t = scope env (Pos.none (P_Abst(xs,t))) in
        _Appl (scope env (Pos.none (P_Abst([(x,None)], u)))) t
  and scope_domain : env -> p_term option -> tbox = fun env t ->
    match t with
    | Some(t) -> scope env t
    | None    ->
        (* We build a metavariable that may use the variables of [env]. *)
        let a = prod_of_env env _Type in
        let vs = Env.vars_of_env env in
        _Meta (fresh_meta a (Array.length vs)) vs
  in
  Bindlib.unbox (scope env t)
