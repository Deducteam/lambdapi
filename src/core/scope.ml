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
  { signature : Sign.t                    (** Current signature.   *)
  ; in_scope  : (sym * Pos.popt) StrMap.t (** Symbols in scope.    *)
  ; aliases   : Path.t StrMap.t           (** Established aliases. *)
  ; builtins  : sym StrMap.t              (** Builtin symbols.     *) }

(** [empty_sig_state] is an empty signature state, without symbols/aliases. *)
let empty_sig_state : Sign.t -> sig_state = fun sign ->
  { signature = sign
  ; in_scope  = StrMap.empty
  ; aliases   = StrMap.empty
  ; builtins  = StrMap.empty }

(** [open_sign ss sign] extends the signature state [ss] with every symbol  of
    the signature [sign].  This has the effect of putting these symbols in the
    scope when (possibly masking symbols with the same name).  Builtin symbols
    are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _ _ v = Some(v) in
  let in_scope = StrMap.union f ss.in_scope Sign.(!(sign.sign_symbols)) in
  let builtins = StrMap.union f ss.builtins Sign.(!(sign.sign_builtins)) in
  {ss with in_scope; builtins}

(** [find_sym ~prt ~prv b st qid] returns the symbol and printing hint
    corresponding to the qualified identifier [qid]. If [fst qid.elt] is
    empty, we search for the name [snd qid.elt] in the opened modules of [st].
    The boolean [b] only indicates if the error message should mention
    variables, in the case where the module path is empty and the symbol is
    unbound. This is reported using the [Fatal] exception.
    {!constructor:Terms.expo.Protec} symbols from other modules
    are allowed in left-hand side of rewrite rules (only) iff [~prt] is true.
    {!constructor:Terms.expo.Privat} symbols are allowed iff [~prv]
    is [true]. *)
let find_sym : prt:bool -> prv:bool -> bool -> sig_state -> qident ->
  sym * pp_hint = fun ~prt ~prv b st qid ->
  let {elt = (mp, s); pos} = qid in
  let mp = List.map fst mp in
  let (s, h) =
    match mp with
    | []                               -> (* Symbol in scope. *)
        begin
          try (fst (StrMap.find s st.in_scope), Nothing) with Not_found ->
          match List.assoc s Unif_hints.map with
          | Symb(s, h)          -> (s, h)
          | _                   -> assert false
          | exception Not_found ->
          let txt = if b then " or variable" else "" in
          fatal pos "Unbound symbol%s [%s]." txt s
        end
    | [m] when StrMap.mem m st.aliases -> (* Aliased module path. *)
        begin
          (* The signature must be loaded (alias is mapped). *)
          let sign =
            try PathMap.find (StrMap.find m st.aliases) Timed.(!Sign.loaded)
            with _ -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try (Sign.find sign s, Alias m) with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Path.pp mp s
        end
    | _                                -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> st.signature.sign_path then
            if not (PathMap.mem mp !(st.signature.sign_deps)) then
              fatal pos "No module [%a] required." Path.pp mp;
          (* The signature must have been loaded. *)
          let sign =
            try PathMap.find mp Timed.(!Sign.loaded)
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try (Sign.find sign s, Qualified) with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Path.pp mp s
        end
  in
  begin
    match (prt, prv, s.sym_expo) with
    | (false, _    , Protec) ->
        if s.sym_path <> st.signature.sign_path then
          (* Fail if symbol is not defined in the current module. *)
          fatal pos "Protected symbol not allowed here."
    | (_    , false, Privat) ->
        fatal pos "Private symbol not allowed here."
    | _                      -> ()
  end;
  (s, h)

(** [find_qid prt prv st env qid] returns a boxed term corresponding to a
    variable of the environment [env] (or to a symbol) which name corresponds
    to [qid]. In the case where the module path [fst qid.elt] is empty, we
    first search for the name [snd qid.elt] in the environment, and if it is
    not mapped we also search in the opened modules. The exception [Fatal] is
    raised if an error occurs (e.g., when the name cannot be found). If [prt]
    is true, {!constructor:Terms.expo.Protec} symbols from
    foreign modules are allowed (protected symbols from current modules are
    always allowed). If [prv] is true,
    {!constructor:Terms.expo.Privat} symbols are allowed. *)
let find_qid : bool -> bool -> sig_state -> env -> qident -> tbox =
  fun prt prv st env qid ->
  let (mp, s) = qid.elt in
  (* Check for variables in the environment first. *)
  try
    if mp <> [] then raise Not_found; (* Variables cannot be qualified. *)
    _Vari (Env.find s env)
  with Not_found ->
    (* Check for symbols. *)
    let (s, hint) = find_sym ~prt ~prv true st qid in
    _Symb s hint

(** [get_root t ss] returns the symbol at the root of term [t]. *)
let get_root : p_term -> sig_state -> sym * pp_hint = fun t ss ->
  let rec get_root t =
    match t.elt with
    | P_Iden(qid,_)
    | P_BinO(_,(_,_,_,qid),_)
    | P_UnaO((_,_,qid),_)   -> find_sym ~prt:true ~prv:true true ss qid
    | P_Appl(t, _)          -> get_root t
    | P_Wrap(t)             -> get_root t
    | _                     -> assert false
  in
  get_root t

(** Data used when scoping a LHS. *)
type m_lhs_data =
  { m_lhs_indices : (string, int   ) Hashtbl.t
  (** Stores the index reserved for a pattern variable of the given name. *)
  ; m_lhs_arities : (int   , int   ) Hashtbl.t
  (** Stores the arity of the pattern variable at the given index. *)
  ; m_lhs_names   : (int   , string) Hashtbl.t
  (** Stores the name of the pattern variable at the given index (if any). *)
  ; mutable m_lhs_size : int
  (** Stores the current known size of the environment of the RHS. *)
  ; m_lhs_in_env  : string list
  (** Pattern variables definitely needed in the RHS environment. *) }

(** Representation of the different scoping modes.  Note that the constructors
    hold specific information for the given mode. *)
type mode =
  | M_Term of meta StrMap.t Stdlib.ref * expo
  (** Standard scoping mode for terms, holding a map of metavariables that can
      be updated with new metavariables on scoping and the exposition of the
      scoped term. *)
  | M_Patt
  (** Scoping mode for patterns in the rewrite tactic. *)
  | M_LHS  of bool * m_lhs_data
  (** Scoping mode for rewriting rule left-hand sides. The constructor carries
      a flag that is set to [true] if {!constructor:Terms.expo.Privat} symbols
      are allowed, and also additional data. *)
  | M_RHS  of bool * (string, tevar) Hashtbl.t
  (** Scoping mode for rewriting rule righ-hand sides. The constructor carries
      a flag that is set to [true] if {!constructor:Terms.expo.Privat} symbols
      are allowed, and the environment for variables that we known to be bound
      in the RHS. *)

(** [get_implicitness t] gives the specified implicitness of the parameters of
    a symbol having the (parser-level) type [t]. *)
let get_implicitness : p_term -> bool list = fun t ->
  let rec get_impl t =
    match t.elt with
    | P_Prod(xs,t) -> List.map (fun (_,_,impl) -> impl) xs @ get_impl t
    | P_Impl(_,t)  -> false :: get_impl t
    | P_Wrap(t)    -> get_impl t
    | _            -> []
  in
  get_impl t

(** [get_args t] decomposes the parser level term [t] into a spine [(h,args)],
    when [h] is the term at the head of the application and [args] is the list
    of all its arguments. Note that sugared applications (e.g., infix symbols)
    are not expanded, so [h] may still be unsugared to an application. *)
let get_args : p_term -> p_term * p_term list =
  let rec get_args args t =
    match t.elt with
    | P_Appl(t,u) -> get_args (u::args) t
    | P_Wrap(t)   -> get_args args t
    | _           -> (t, args)
  in get_args []

(** [scope md ss env t] turns a parser-level term [t] into an actual term. The
    variables of the environment [env] may appear in [t], and the scoping mode
    [md] changes the behaviour related to certain constructors.  The signature
    state [ss] is used to hande module aliasing according to [find_qid]. *)
let scope : mode -> sig_state -> env -> p_term -> tbox = fun md ss env t ->
  (* Unique pattern variable generation for wildcards in a LHS. *)
  let fresh_patt data name env =
    let fresh_index () =
      let i = data.m_lhs_size in
      data.m_lhs_size <- i + 1;
      let arity = Array.length env in
      Hashtbl.add data.m_lhs_arities i arity; i
    in
    match name with
    | Some(name) ->
        let i =
          try Hashtbl.find data.m_lhs_indices name with Not_found ->
          let i = fresh_index () in
          Hashtbl.add data.m_lhs_indices name i;
          Hashtbl.add data.m_lhs_names i name; i
        in
        _Patt (Some(i)) (Printf.sprintf "%i_%s" i name) env
    | None       ->
        let i = fresh_index () in
        _Patt (Some(i)) (Printf.sprintf "%i" i) env
  in
  (* Toplevel scoping function, with handling of implicit arguments. *)
  let rec scope : env -> p_term -> tbox = fun env t ->
    (* Extract the spine. *)
    let (p_head, args) = get_args t in
    (* Check that LHS pattern variables are applied to no argument. *)
    begin
      match (p_head.elt, md) with
      | (P_Patt(_,_), M_LHS(_)) when args <> [] ->
          fatal t.pos "Pattern variables cannot be applied."
      | _                                       -> ()
    end;
    (* Scope the head and obtain the implicitness of arguments. *)
    let h = scope_head env p_head in
    let impl =
      (* Check whether application is marked as explicit in head symbol. *)
      let expl = match p_head.elt with P_Iden(_,b) -> b | _ -> false in
      (* We avoid unboxing if [h] is not closed (and hence not a symbol). *)
      if expl || not (Bindlib.is_closed h) then [] else
      match Bindlib.unbox h with Symb(s,_) -> s.sym_impl | _ -> []
    in
    (* Scope and insert the (implicit) arguments. *)
    add_impl env t.pos h impl args
  (* Build the application of [h] to [args], inserting implicit arguments. *)
  and add_impl env loc h impl args =
    let appl_p_term t u = _Appl t (scope env u) in
    let appl_meta t = _Appl t (scope_head env (Pos.none P_Wild)) in
    match (impl, args) with
    (* The remaining arguments are all explicit. *)
    | ([]         , _      ) -> List.fold_left appl_p_term h args
    (* Only implicit arguments remain. *)
    | (true ::impl, []     ) -> add_impl env loc (appl_meta h) impl []
    (* The first argument is implicit (could be [a] if made explicit). *)
    | (true ::impl, a::args) ->
        begin
          match a.elt with
          | P_Expl(a) -> add_impl env loc (appl_p_term h a) impl args
          | _         -> add_impl env loc (appl_meta h) impl (a::args)
        end
    (* The first argument [a] is explicit. *)
    | (false::impl, a::args) ->
        begin
          match a.elt with
          | P_Expl(_) -> fatal a.pos "Unexpected explicit argument."
          | _         -> add_impl env loc (appl_p_term h a) impl args
        end
    (* The application is too "partial" to insert all implicit arguments. *)
    | (false::_   , []     ) ->
        (* NOTE this could be improved with more general implicits. *)
        fatal loc "More arguments are required to instantiate implicits."
  (* Scoping function for the domain of functions or products. *)
  and scope_domain : env -> p_term option -> tbox = fun env a ->
    match (a, md) with
    | (Some(a), M_LHS(_)    ) ->
        fatal a.pos "Annotation not allowed in a LHS."
    | (None   , M_LHS(_,d)  ) -> fresh_patt d None (Env.to_tbox env)
    | (Some(a), _           ) -> scope env a
    | (None   , _           ) ->
        (* Create a new metavariable of type [TYPE] for the missing domain. *)
        let vs = Env.to_tbox env in
        let a = Env.to_prod_box env _Type in
        let m = _Meta_full (fresh_meta_box a (Array.length vs)) vs in
        (* Sanity check: only variables of [env] free in [m] if not in RHS. *)
        match md with
        | M_RHS(_,_) -> m
        | _          ->
        assert (Bindlib.is_closed (Bindlib.bind_mvar (Env.vars env) m)); m
  (* Scoping of a binder (abstraction or product). The environment made of the
     variables is also returned. *)
  and scope_binder cons env xs t =
    let rec aux env xs =
      match xs with
      | []                  -> (scope env t, [])
      | ([]       ,_,_)::xs -> aux env xs
      | (None  ::l,d,i)::xs ->
          let v = Bindlib.new_var mkfree "_" in
          let a = scope_domain env d in
          let (t,env) = aux env ((l,d,i)::xs) in
          (cons a (Bindlib.bind_var v t), Env.add v a None env)
      | (Some x::l,d,i)::xs ->
          let v = Bindlib.new_var mkfree x.elt in
          let a = scope_domain env d in
          let (t,env) =
            aux ((x.elt,(v,a,None)) :: env) ((l,d,i) :: xs)
          in
          if x.elt.[0] <> '_' && not (Bindlib.occur v t) then
            wrn x.pos "Variable [%s] could be replaced by [_]." x.elt;
          (cons a (Bindlib.bind_var v t), Env.add v a None env)
    in
    aux env xs
  (* Scoping function for head terms. *)
  and scope_head : env -> p_term -> tbox = fun env t ->
    match (t.elt, md) with
    | (P_Type          , M_LHS(_)         ) ->
        fatal t.pos "[%a] is not allowed in a LHS." Print.pp Type
    | (P_Type          , _                ) -> _Type
    | (P_Iden(qid,_)   , M_LHS(p,_)       ) -> find_qid true p ss env qid
    | (P_Iden(qid,_)   , M_Term(_,Privat )) -> find_qid false true ss env qid
    | (P_Iden(qid,_)   , M_RHS(p,_)       ) -> find_qid false p ss env qid
    | (P_Iden(qid,_)   , _                ) -> find_qid false false ss env qid
    | (P_Wild          , M_LHS(_,d)       ) ->
        fresh_patt d None (Env.to_tbox env)
    | (P_Wild          , M_Patt           ) -> _Wild
    | (P_Wild          , _                ) ->
        (* We create a metavariable [m] of type [tm], which itself is also a
           metavariable [x] of type [Type].  Note that this case applies both
           to regular terms, and to the RHS of rewriting rules. *)
        let vs = Env.to_tbox env in
        let arity = Array.length vs in
        let tm =
          let x = fresh_meta_box (Env.to_prod_box env _Type) arity in
          Env.to_prod_box env (_Meta_full x vs)
        in
        let m = _Meta_full (fresh_meta_box tm arity) vs in
        (* Sanity check: only variables of [env] free in [m] if not in RHS. *)
        begin
          match md with
          | M_RHS(_,_) -> m
          | _          ->
          assert (Bindlib.is_closed (Bindlib.bind_mvar (Env.vars env) m)); m
        end
    | (P_Meta(id,ts)   , M_Term(m,_)      ) ->
        let m2 =
          (* We first check if the metavariable is in the map. *)
          try StrMap.find id.elt Stdlib.(!m) with Not_found ->
          (* Otherwise we create a new metavariable [m1] of type [TYPE]
             and a new metavariable [m2] of name [id] and type [m1], and
             return [m2]. *)
          let vs = Env.to_tbox env in
          let m1 = fresh_meta (Env.to_prod env _Type) (Array.length vs) in
          let a = Env.to_prod env (_Meta m1 vs) in
          let m2 = fresh_meta ~name:id.elt a (Array.length vs) in
          Stdlib.(m := StrMap.add id.elt m2 !m); m2
        in
        _Meta m2 (Array.map (scope env) ts)
    | (P_Meta(_,_)     , _                ) ->
        fatal t.pos "Metavariables are not allowed in rewriting rules."
    | (P_Patt(id,ts)   , M_LHS(_,d)       ) ->
        (* Check that [ts] are variables. *)
        let scope_var t =
          match unfold (Bindlib.unbox (scope env t)) with
          | Vari(x) -> x
          | _       -> fatal t.pos "Only bound variables are allowed in the \
                                    environment of pattern variables."
        in
        let vs = Array.map scope_var ts in
        (* Check that [vs] are distinct variables. *)
        for i = 0 to Array.length vs - 2 do
          for j = i + 1 to Array.length vs - 1 do
            if Bindlib.eq_vars vs.(i) vs.(j) then
              let name = Bindlib.name_of vs.(j) in
              fatal ts.(j).pos "Variable %s appears more than once in the \
                                environment of a pattern variable." name
          done
        done;
        let ar = Array.map Bindlib.box_var vs in
        begin
          match id with
          | None     when List.length env = Array.length vs    ->
              wrn t.pos "Pattern [%a] could be replaced by [_]." Pretty.pp t;
          | Some(id) when not (List.mem id.elt d.m_lhs_in_env) ->
              if List.length env = Array.length vs then
                wrn t.pos "Pattern variable [%a] can be replaced by a \
                           wildcard [_]." Pretty.pp t
              else
                wrn t.pos "Pattern variable [$%s] does not need to be \
                           named." id.elt
          | _                                                  -> ()
        end;
        fresh_patt d (Option.map (fun id -> id.elt) id) ar
    | (P_Patt(id,ts)   , M_RHS(_,h)         ) ->
        let x =
          match id with
          | None     -> fatal t.pos "Wildcard pattern not allowed in a RHS."
          | Some(id) ->
          try Hashtbl.find h id.elt with Not_found ->
            fatal t.pos "Pattern variable not in scope."
        in
        _TEnv (Bindlib.box_var x) (Array.map (scope env) ts)
    | (P_Patt(_,_)     , _                  ) ->
        fatal t.pos "Pattern variables are only allowed in rewriting rules."
    | (P_Appl(_,_)     , _                  ) ->
        assert false (* Unreachable. *)
    | (P_Impl(_,_)     , M_LHS(_)           ) ->
        (* FIXME: should be allowed for hints *)
        fatal t.pos "Implications are not allowed in a LHS."
    | (P_Impl(_,_)     , M_Patt             ) ->
        fatal t.pos "Implications are not allowed in a pattern."
    | (P_Impl(a,b)     , _                  ) ->
        _Impl (scope env a) (scope env b)
    | (P_Abst(_,_)     , M_Patt             ) ->
        fatal t.pos "Abstractions are not allowed in a pattern."
    | (P_Abst(xs,t)    , _                  ) ->
        fst (scope_binder _Abst env xs t)
    | (P_Prod(_,_)     , M_LHS(_)           ) ->
        fatal t.pos "Dependent products are not allowed in a LHS."
    | (P_Prod(_,_)     , M_Patt             ) ->
        fatal t.pos "Dependent products are not allowed in a pattern."
    | (P_Prod(xs,b)    , _                  ) ->
        fst (scope_binder _Prod env xs b)
    | (P_LLet(x,xs,a,t,u), M_Term(_)        )
    | (P_LLet(x,xs,a,t,u), M_RHS(_)         ) ->
        let a =
          let a = Option.get (Pos.none P_Wild) a in
          scope env (if xs = [] then a else Pos.none (P_Prod(xs, a)))
        in
        let t = scope env (if xs = [] then t else Pos.none (P_Abst(xs, t))) in
        let v = Bindlib.new_var mkfree x.elt in
        let u = scope (Env.add v a (Some(t)) env) u in
        if not (Bindlib.occur v u) then
          wrn x.pos "Useless let-binding ([%s] not bound)." x.elt;
        _LLet a t (Bindlib.bind_var v u)
    | (P_LLet(_)       , M_LHS(_)           ) ->
        fatal t.pos "Let-bindings are not allowed in a LHS."
    | (P_LLet(_)       , M_Patt             ) ->
        fatal t.pos "Let-bindings are not allowed in a pattern."
    | (P_NLit(n)       , _                  ) ->
        let sym_z = _Symb (Builtin.get t.pos ss.builtins "0") Nothing
        and sym_s = _Symb (Builtin.get t.pos ss.builtins "+1") Nothing in
        let rec unsugar_nat_lit acc n =
          if n <= 0 then acc else unsugar_nat_lit (_Appl sym_s acc) (n-1)
        in
        unsugar_nat_lit sym_z n
    | (P_UnaO(u,t)    , _                   ) ->
        let (s, impl) =
          let (op,_,qid) = u in
          let (s, _) = find_sym ~prt:true ~prv:true true ss qid in
          (_Symb s (Unary(op)), s.sym_impl)
        in
        add_impl env t.pos s impl [t]
    | (P_BinO(l,b,r)  , _                   ) ->
        let (s, impl) =
          let (op,_,_,qid) = b in
          let (s, _) = find_sym ~prt:true ~prv:true true ss qid in
          (_Symb s (Binary(op)), s.sym_impl)
        in
        add_impl env t.pos s impl [l; r]
    | (P_Wrap(t)      , _                   ) -> scope env t
    | (P_Expl(_)      , _                   ) ->
        fatal t.pos "Explicit argument not allowed here."
  in
  scope env t

(** [scope ?exp ss env t] turns a parser-level term [t] into an actual term.
    The variables of the environment [env] may appear in [t]. The signature
    state [ss] is used to handle module aliasing according to [find_qid]. If
    [?exp] is {!constructor:Public}, then the term mustn't contain any private
    subterms. *)
let scope_term : expo -> sig_state -> env -> p_term -> term =
  fun expo ss env t ->
  let m = Stdlib.ref StrMap.empty in
  Bindlib.unbox (scope (M_Term(m, expo)) ss env t)

(** [patt_vars t] returns a couple [(pvs,nl)]. The first compoment [pvs] is an
    association list giving the arity of all the “pattern variables” appearing
    in the parser-level term [t]. The second component [nl] contains the names
    of the “pattern variables” that appear non-linearly.  If a given  “pattern
    variable” occurs with different arities the program fails gracefully. *)
let patt_vars : p_term -> (string * int) list * string list =
  let rec patt_vars acc t =
    match t.elt with
    | P_Type             -> acc
    | P_Iden(_)          -> acc
    | P_Wild             -> acc
    | P_Meta(_,ts)       -> Array.fold_left patt_vars acc ts
    | P_Patt(id,ts)      -> add_patt (Array.fold_left patt_vars acc ts) id ts
    | P_Appl(t,u)        -> patt_vars (patt_vars acc t) u
    | P_Impl(a,b)        -> patt_vars (patt_vars acc a) b
    | P_Abst(xs,t)       -> patt_vars (arg_patt_vars acc xs) t
    | P_Prod(xs,b)       -> patt_vars (arg_patt_vars acc xs) b
    | P_LLet(_,xs,a,t,u) ->
        let pvs = patt_vars (patt_vars (arg_patt_vars acc xs) t) u in
        begin
          match a with
          | None    -> pvs
          | Some(a) -> patt_vars pvs a
        end
    | P_NLit(_)          -> acc
    | P_UnaO(_,t)        -> patt_vars acc t
    | P_BinO(t,_,u)      -> patt_vars (patt_vars acc t) u
    | P_Wrap(t)          -> patt_vars acc t
    | P_Expl(t)          -> patt_vars acc t
  and add_patt ((pvs, nl) as acc) id ts =
    match id with
    | None     -> acc
    | Some(id) ->
    try
      if List.assoc id.elt pvs <> Array.length ts then
        fatal id.pos "Arity mismatch for pattern variable [%s]." id.elt;
      if List.mem id.elt nl then acc else (pvs, id.elt :: nl)
    with Not_found -> ((id.elt, Array.length ts) :: pvs, nl)
  and arg_patt_vars acc xs =
    match xs with
    | []                    -> acc
    | (_, None   , _) :: xs -> arg_patt_vars acc xs
    | (_, Some(a), _) :: xs -> arg_patt_vars (patt_vars acc a) xs
  in
  patt_vars ([],[])

(** Representation of a rewriting rule prior to SR-checking. *)
type pre_rule =
  { pr_sym     : sym * pp_hint
  (** Head symbol of the LHS with its printing hint. *)
  ; pr_lhs     : term list
  (** Arguments of the LHS. *)
  ; pr_vars    : term_env Bindlib.mvar
  (** Pattern variables that can appear in the RHS. *)
  ; pr_rhs     : tbox
  (** Body of the RHS, should only be unboxed once. *)
  ; pr_names   : (int, string) Hashtbl.t
  (** Gives the original name (if any) of pattern variable at given index. *)
  ; pr_arities : int array
  (** Gives the arity of all the pattern varialbes in field [pr_vars]. *) }

(** [scope_rule ss r] turns a parser-level rewriting rule [r] into a rewriting
    rule (and the associated head symbol). *)
let scope_rule : sig_state -> p_rule -> pre_rule loc = fun ss r ->
  let (p_lhs, p_rhs) = r.elt in
  (* Compute the set of pattern variables on both sides. *)
  let (pvs_lhs, nl) = patt_vars p_lhs in
  (* NOTE to reject non-left-linear rules check [nl = []] here. *)
  let (pvs_rhs, _ ) = patt_vars p_rhs in
  (* Check that pattern variables of RHS exist LHS (with right arities). *)
  let check_in_lhs (m,i) =
    let j =
      try List.assoc m pvs_lhs with Not_found ->
      fatal p_rhs.pos "Unknown pattern variable [%s]." m
    in
    if i <> j then fatal p_lhs.pos "Arity mismatch for [%s]." m
  in
  List.iter check_in_lhs pvs_rhs;
  (* Get privacy of head of the rule, scope the rest accordingly. *)
  let prv = is_private (fst (get_root p_lhs ss)) in
  (* Scope the LHS and get the reserved index for named pattern variables. *)
  let (pr_lhs, data) =
    let data =
      { m_lhs_indices = Hashtbl.create 7
      ; m_lhs_arities = Hashtbl.create 7
      ; m_lhs_names   = Hashtbl.create 7
      ; m_lhs_size    = 0
      ; m_lhs_in_env  = nl @ (List.map fst pvs_rhs) }
    in
    let pr_lhs = scope (M_LHS(prv, data)) ss Env.empty p_lhs in
    (Bindlib.unbox pr_lhs, data)
  in
  (* Check the head symbol and build actual LHS. *)
  let (sym, hint, pr_lhs) =
    let (h, args) = Basics.get_args pr_lhs in
    match h with
    | Symb(s,h) ->
        if is_constant s then
          fatal p_lhs.pos "Constant LHS head symbol.";
        if s.sym_expo = Protec && ss.signature.sign_path <> s.sym_path then
          fatal p_lhs.pos "Cannot define rules on foreign protected symbols.";
        (s, h, args)
    | _         ->
        fatal p_lhs.pos "No head symbol in LHS."
  in
  if pr_lhs = [] then wrn p_lhs.pos "LHS head symbol with no argument.";
  (* Create the pattern variables that can be bound in the RHS. *)
  let pr_vars =
    let fn i =
      let name =
        try Printf.sprintf "%i_%s" i (Hashtbl.find data.m_lhs_names i)
        with Not_found -> Printf.sprintf "%i" i
      in
      Bindlib.new_var te_mkfree name
    in
    Array.init data.m_lhs_size fn
  in
  (* We scope the RHS. *)
  let pr_rhs =
    let mode =
      let htbl_vars = Hashtbl.create (Hashtbl.length data.m_lhs_indices) in
      let fn k i = Hashtbl.add htbl_vars k pr_vars.(i) in
      Hashtbl.iter fn data.m_lhs_indices;
      M_RHS(is_private sym, htbl_vars)
    in
    scope mode ss Env.empty p_rhs
  in
  (* We put everything together to build the pre-rule. *)
  let pr_arities =
    let fn i =
      try Hashtbl.find data.m_lhs_arities i
      with Not_found -> assert false (* Unreachable. *)
    in
    Array.init data.m_lhs_size fn
  in
  let pr =
    { pr_sym = (sym, hint) ; pr_lhs ; pr_vars ; pr_rhs ; pr_arities
    ; pr_names = data.m_lhs_names }
  in
  Pos.make r.pos pr

(** [scope_hint ss h] transforms a parser-level hint [h] into a rewriting rule
    defined on {!val:Sign.hint_unif}. A unification hint can be seen as a
    rewriting rule that rewrite a unification problem into one or more
    sub-unification problems. *)
let scope_hint : sig_state -> p_hint -> rule loc = fun ss h ->
  let (p_l, p_rs) = h.elt in
  (* NOTE: in the following comments, we consider a unification hint of the
     form P ≡ Q → x1 ≡ H1, ..., xn ≡ Hn. *)
  (* Compute the pattern variables. *)
  let data =
    (* Get pattern variables of [l] and [r] and verify that they are
       linear. *)
    let lin_patt_vars (l,r) =
      let (pvs_l, nl) = patt_vars l in
      if nl <> [] then fatal p_l.pos "Linear unification hints only.";
      let (pvs_r, nl) = patt_vars r in
      if nl <> [] then fatal p_rs.pos "Linear unification hints only.";
      pvs_l @ pvs_r
    in
    let pvs_lhs = lin_patt_vars p_l.elt in
    let pvs_rhs = List.concat (List.map lin_patt_vars p_rs.elt) in
    let check_in_lhs (m,_) =
      try ignore (List.assoc m pvs_lhs) with Not_found ->
      fatal p_rs.pos "Unknown pattern variable [%s]." m
    in
    List.iter check_in_lhs pvs_rhs;
    { m_lhs_indices = Hashtbl.create 7
    ; m_lhs_arities = Hashtbl.create 7
    ; m_lhs_names   = Hashtbl.create 7
    ; m_lhs_size    = 0
    ; m_lhs_in_env  = List.map fst pvs_rhs }
  in
  (* Like [Basics.add_args] but for parser level terms. *)
  let add_args t args =
    let rec add_args t args =
      match args with
      | []      -> t
      | u::args -> add_args (Pos.none (P_Appl(t,u))) args
    in
    add_args t args
  in
  (* [mk_unif_pb (l,r)] creates a parser-level unification problem [l ≡ r]. *)
  let mk_unif_pb (l,r) = add_args Syntax.Unif_hints.p_atom [l; r] in
  let lhs =
    let lhs =
      let p_lhs = mk_unif_pb p_l.elt in
      Bindlib.unbox (scope (M_LHS(true, data)) ss Env.empty p_lhs)
    in
    let (h, args) = Basics.get_args lhs in
    assert (match h with
        | Symb(s,_) -> s == Basics.to_sym Unif_hints.atom
        | _ -> false);
    args
  in
  let vars =
    let fn i =
      let name =
        try Printf.sprintf "%i_%s" i (Hashtbl.find data.m_lhs_names i)
        with Not_found -> Printf.sprintf "%i" i
      in
      Bindlib.new_var te_mkfree name
    in
    Array.init data.m_lhs_size fn
  in
  (* The rhs is of the form
     - either [x ≡ t], or
     - [x ≡ t, y ≡ u, ...]
     where [x] and [y] are pattern variables. *)
  let rhs : (term_env, term) Bindlib.mbinder =
    let rhs =
      let p_rhs =
        let unif_probs = List.map mk_unif_pb p_rs.elt in
        add_args Syntax.Unif_hints.p_list unif_probs
      in
      let mode =
        let htbl_vars = Hashtbl.create (Hashtbl.length data.m_lhs_indices) in
        let fn k i = Hashtbl.add htbl_vars k vars.(i) in
        Hashtbl.iter fn data.m_lhs_indices;
        M_RHS(true, htbl_vars) in
      scope mode ss Env.empty p_rhs
    in
    Bindlib.unbox (Bindlib.bind_mvar vars rhs)
  in
  let arities =
    let fn i =
      try Hashtbl.find data.m_lhs_arities i
      with Not_found -> assert false (* Unreachable. *)
    in
    Array.init data.m_lhs_size fn
  in
  (* NOTE: the remaining of the function checks whether [lhs] and [rhs] are
     well-formed. *)
  let _, rhst = Bindlib.unmbind rhs in
  (* Retrieve the sub unification problems in the form (xi, Hi). *)
  let bindings : (tevar * term) list =
    let (h, args) = Basics.get_args rhst in
    assert (Basics.to_sym h == Basics.to_sym Unif_hints.list);
    let f t = (* [f (xi ≡ Hi)] returns [(xi, Hi)] *)
      match Basics.get_args t with
      | (Symb(s, _), [TEnv(TE_Vari(x),_); u]) ->
          assert (s == Basics.to_sym Unif_hints.atom);
          (x, u)
      | _                                     ->
          assert false (* Ill-formed hint. *)
    in
    List.map f args
  in
  (* Ensure that (xi)i are distinct pairwise. *)
  let eq_fst (x,_) (y,_) = Bindlib.eq_vars x y in
  if not (List.are_distinct ~eq:eq_fst bindings) then
    fatal p_rs.pos "Only linear hint RHS allowed";
  (* [vars_closed (_,t)] raises an error if [t] depends on a variable in
     [bvars]. *)
  let bvars = List.map fst bindings in
  let vars_closed (_,t) =
    let tb = lift t in
    if List.exists (fun x -> Bindlib.occur x tb) bvars then
      fatal p_rs.pos
        "RHS of sub-unification problems can't depend on hinted vars"
  in
  (* Ensure that ∀ (i, j), Hi does not depend on xj. *)
  List.iter vars_closed bindings;
  (* [subst_from_hints t] substitutes pattern variables in [t] by the values
     in [bindings]. *)
  (* FIXME: rather replace by meta variables and check type (as with SR). *)
  let subst_of_hints t =
    let rec subst t =
      match unfold t with
      | Appl(t,u)         -> Appl(subst t, subst u)
      | Patt(Some(_),s,_) -> (* Only variables used in rhs. *)
          let f (x,_) = String.equal s (Bindlib.name_of x) in
          snd (try List.find f bindings with Not_found -> assert false)
      | t           -> t
    in
    subst t
  in
  (* Ensure that hints are sound, that is, P[x1 ≔ H1, ..., xn ≔ Hn] is
     convertible with Q[x1 ≔ H1, ..., xn ≔ Hn]. *)
  begin match lhs with
    | [t; u] ->
      let pp_binding oc (tev, t) =
        Format.fprintf oc "@[$%a ≔ %a@]" Print.pp_tevar tev Print.pp t
      in
      if not (Eval.eq_modulo [] (subst_of_hints t) (subst_of_hints u)) then
        fatal h.pos ("[%a]@ is@ not@ convertible@ with@ [%a]@ " ^^
                     "with@ substitution@ [%a]")
          Print.pp t Print.pp u (List.pp pp_binding ", ") bindings
    | _      -> assert false
  end;
  Pos.make h.pos {lhs; rhs; arity = List.length lhs; vars; arities}

(** [scope_pattern ss env t] turns a parser-level term [t] into an actual term
    that will correspond to selection pattern (rewrite tactic). *)
let scope_pattern : sig_state -> env -> p_term -> term = fun ss env t ->
  Bindlib.unbox (scope M_Patt ss env t)

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
let scope_rw_patt : sig_state ->  env -> p_rw_patt loc -> Rewrite.rw_patt =
    fun ss env s ->
  let open Rewrite in
  match s.elt with
  | P_rw_Term(t)               -> RW_Term(scope_pattern ss env t)
  | P_rw_InTerm(t)             -> RW_InTerm(scope_pattern ss env t)
  | P_rw_InIdInTerm(x,t)       ->
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      RW_InIdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_rw_IdInTerm(x,t)         ->
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      RW_IdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_rw_TermInIdInTerm(u,x,t) ->
      let u = scope_pattern ss env u in
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      RW_TermInIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | P_rw_TermAsIdInTerm(u,x,t) ->
      let u = scope_pattern ss env u in
      let v = Bindlib.new_var mkfree x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      RW_TermAsIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
