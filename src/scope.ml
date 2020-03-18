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
  ; aliases   : module_path StrMap.t      (** Established aliases. *)
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
  let fn _ v _ = Some(v) in
  let in_scope = StrMap.union fn ss.in_scope Sign.(!(sign.sign_symbols)) in
  let builtins = StrMap.union fn ss.builtins Sign.(!(sign.sign_builtins)) in
  {ss with in_scope; builtins}

(** [find_sym ~prt ~prv b st qid] returns the symbol and printing hint
    corresponding to the qualified identifier [qid]. If [fst qid.elt] is
    empty, we search for the name [snd qid.elt] in the opened modules of [st].
    The boolean [b] only indicates if the error message should mention
    variables, in the case where the module path is empty and the symbol is
    unbound. This is reported using the [Fatal] exception.
    {!constructor:Terms.sym_exposition.Protected} symbols from other modules
    are allowed in left-hand side of rewrite rules (only) iff [~prt] is true.
    {!constructor:Terms.sym_exposition.Private} symbols are allowed iff [~prv]
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
          try (List.assoc s Sign.Unif_hints.map, Nothing) with Not_found ->
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
          fatal pos "Unbound symbol [%a.%s]." Files.pp_path mp s
        end
    | _                                -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> st.signature.sign_path then
            if not (PathMap.mem mp !(st.signature.sign_deps)) then
              fatal pos "No module [%a] required." Files.pp_path mp;
          (* The signature must have been loaded. *)
          let sign =
            try PathMap.find mp Timed.(!Sign.loaded)
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try (Sign.find sign s, Qualified) with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Files.pp_path mp s
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
    is true, {!constructor:Terms.sym_exposition.Protected} symbols from
    foreign modules are allowed (protected symbols from current modules are
    always allowed). If [prv] is true,
    {!constructor:Terms.sym_exposition.Private} symbols are allowed. *)
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

(** Map of metavariables. *)
type metamap = meta StrMap.t

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

(** Representation of the different scoping modes.  Note that the constructors
    hold specific information for the given mode. *)
type mode =
  | M_Term of metamap Pervasives.ref * expo
  (** Standard scoping mode for terms, holding a map of metavariables that can
      be updated with new metavariables on scoping and the exposition of the
      scoped term. *)
  | M_Patt
  (** Scoping mode for patterns in the rewrite tactic. *)
  | M_LHS  of (string * int) list * bool
  (** Scoping mode for rewriting rule left-hand sides. The constructor carries
      a map associating an index to every free variable along with a flag set
      to [true] if {!constructor:Terms.sym_exposition.Private} symbols are
      allowed. *)
  | M_RHS  of (string * tevar) list * bool
  (** Scoping mode for rewriting rule righ-hand sides. The constructor carries
      the environment for variables that will be bound in the representation
      of the RHS along with a flag indicating whether
      {!constructor:Terms.sym_exposition.Private} terms are allowed. *)

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
  let fresh_patt_name =
    let c = Pervasives.ref (-1) in
    fun _ -> Pervasives.(incr c; Printf.sprintf "#%i" !c)
  in
  let fresh_patt env = _Patt None (fresh_patt_name ()) (Env.to_tbox env) in
  (* Toplevel scoping function, with handling of implicit arguments. *)
  let rec scope : env -> p_term -> tbox = fun env t ->
    (* Extract the spine. *)
    let (p_head, args) = get_args t in
    (* Check that LHS pattern variables are applied to no argument. *)
    begin
      match (p_head.elt, md) with
      | (P_Patt(_,_), M_LHS(_,_)) when args <> [] ->
          fatal t.pos "Pattern variables cannot be applied."
      | _                                         -> ()
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
    | (Some(a), M_LHS(_)) -> fatal a.pos "Annotation not allowed in a LHS."
    | (None   , M_LHS(_)) -> fresh_patt env
    | (Some(a), _       ) -> scope env a
    | (None   , _       ) ->
        (* Create a new metavariable of type [TYPE] for the missing domain. *)
        let vs = Env.to_tbox env in
        _Meta (fresh_meta (Env.to_prod env _Type) (Array.length vs)) vs
  (* Scoping of a binder (abstraction or product). *)
  and scope_binder cons env xs t =
    let rec aux env xs =
      match xs with
      | []                  -> scope env t
      | ([]       ,_,_)::xs -> aux env xs
      | (None  ::l,d,i)::xs ->
          let v = Bindlib.new_var mkfree "_" in
          let a = scope_domain env d in
          let t = aux env ((l,d,i)::xs) in
          cons a (Bindlib.bind_var v t)
      | (Some x::l,d,i)::xs ->
          let v = Bindlib.new_var mkfree x.elt in
          let a = scope_domain env d in
          let t = aux ((x.elt,(v,a)) :: env) ((l,d,i) :: xs) in
          if x.elt.[0] <> '_' && not (Bindlib.occur v t) then
            wrn x.pos "Variable [%s] could be replaced by [_]." x.elt;
          cons a (Bindlib.bind_var v t)
    in
    aux env xs
  (* Scoping function for head terms. *)
  and scope_head : env -> p_term -> tbox = fun env t ->
    match (t.elt, md) with
    | (P_Type          , M_LHS(_)         ) ->
        fatal t.pos "[%a] is not allowed in a LHS." Print.pp Type
    | (P_Type          , _                ) -> _Type
    | (P_Iden(qid,_)   , M_LHS(_,p)       ) -> find_qid true p ss env qid
    | (P_Iden(qid,_)   , M_Term(_,Privat )) -> find_qid false true ss env qid
    | (P_Iden(qid,_)   , M_RHS(_,p)       ) -> find_qid false p ss env qid
    | (P_Iden(qid,_)   , _                ) -> find_qid false false ss env qid
    | (P_Wild          , M_LHS(_)         ) -> fresh_patt env
    | (P_Wild          , M_Patt           ) -> _Wild
    | (P_Wild          , _                ) ->
        (* We create a metavariable [m] of type [m_ty], which is itself also a
           metavariable (of type [Type]).  Note that this case applies both to
           regular terms, and to the RHS of rewriting rules. *)
        let vs = Env.to_tbox env in
        let m_ty = fresh_meta (Env.to_prod env _Type) (Array.length vs) in
        let a = Env.to_prod env (_Meta m_ty vs) in
        let m = fresh_meta a (Array.length vs) in
        _Meta m vs
    | (P_Meta(id,ts)   , M_Term(m,_)      ) ->
        let m2 =
          (* We first check if the metavariable is in the map. *)
          try StrMap.find id.elt Pervasives.(!m) with Not_found ->
          (* Otherwise we create a new metavariable [m1] of type [TYPE]
             and a new metavariable [m2] of name [id] and type [m1], and
             return [m2]. *)
          let vs = Env.to_tbox env in
          let m1 = fresh_meta (Env.to_prod env _Type) (Array.length vs) in
          let a = Env.to_prod env (_Meta m1 vs) in
          let m2 = fresh_meta ~name:id.elt a (Array.length vs) in
          Pervasives.(m := StrMap.add id.elt m2 !m); m2
        in
        _Meta m2 (Array.map (scope env) ts)
    | (P_Meta(_,_)     , _                ) ->
        fatal t.pos "Metavariables are not allowed in rewriting rules."
    | (P_Patt(id,ts)   , M_LHS(m,_)       ) ->
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
        (* Find the reserved index, if any. *)
        begin
          match id with
          | None     ->
              if List.length env = Array.length vs then
                wrn t.pos "Pattern [%a] could be replaced by [_]."
                  Pretty.pp_p_term t;
              _Patt None (fresh_patt_name ()) (Array.map Bindlib.box_var vs)
          | Some(id) ->
              let i =
                try Some(List.assoc id.elt m) with Not_found ->
                  if List.length env = Array.length vs then
                    wrn t.pos "Pattern variable [%a] can be replaced by a \
                               wildcard [_]." Pretty.pp_p_term t
                  else
                    wrn t.pos "Pattern variable [&%s] does not need to be \
                               named." id.elt;
                  None
              in
              _Patt i id.elt (Array.map Bindlib.box_var vs)
        end
    | (P_Patt(id,ts)   , M_RHS(m,_)       ) ->
        let x =
          match id with
          | None     -> fatal t.pos "Wildcard pattern not allowed in a RHS."
          | Some(id) -> try List.assoc id.elt m with Not_found ->
                          fatal t.pos "Pattern variable not in scope."
        in
        _TEnv (Bindlib.box_var x) (Array.map (scope env) ts)
    | (P_Patt(_,_)     , _                ) ->
        fatal t.pos "Pattern variables are only allowed in rewriting rules."
    | (P_Appl(_,_)     , _                ) -> assert false (* Unreachable. *)
    | (P_Impl(_,_)     , M_LHS(_)         ) ->
        fatal t.pos "Implications are not allowed in a LHS."
    | (P_Impl(_,_)     , M_Patt           ) ->
        fatal t.pos "Implications are not allowed in a pattern."
    | (P_Impl(a,b)     , _                ) ->
        _Impl (scope env a) (scope env b)
    | (P_Abst(_,_)     , M_Patt           ) ->
        fatal t.pos "Abstractions are not allowed in a pattern."
    | (P_Abst(xs,t)    , _                ) -> scope_binder _Abst env xs t
    | (P_Prod(_,_)     , M_LHS(_)         ) ->
        fatal t.pos "Dependent products are not allowed in a LHS."
    | (P_Prod(_,_)     , M_Patt           ) ->
        fatal t.pos "Dependent products are not allowed in a pattern."
    | (P_Prod(xs,b)    , _                ) -> scope_binder _Prod env xs b
    | (P_LLet(x,xs,t,u), M_Term(_)        )
    | (P_LLet(x,xs,t,u), M_RHS(_)         ) ->
        (* Scope the binding [x xs := t] *)
        let t = scope_binder _Abst env xs t in
        (* Scope all the [let x xs := t in u] *)
        let cons a u = _LLet t a u in
        scope_binder cons env [[Some(x)], None, false] u
    | (P_LLet(_)       , M_LHS(_)         ) ->
        fatal t.pos "Let-bindings are not allowed in a LHS."
    | (P_LLet(_)       , M_Patt           ) ->
        fatal t.pos "Let-bindings are not allowed in a pattern."
    | (P_NLit(n)       , _                ) ->
        let sym_z = _Symb (Sign.builtin t.pos ss.builtins "0") Nothing
        and sym_s = _Symb (Sign.builtin t.pos ss.builtins "+1") Nothing in
        let rec unsugar_nat_lit acc n =
          if n <= 0 then acc else unsugar_nat_lit (_Appl sym_s acc) (n-1)
        in
        unsugar_nat_lit sym_z n
    | (P_UnaO(u,t)    , _                 ) ->
        let (s, impl) =
          let (op,_,qid) = u in
          let (s, _) = find_sym ~prt:true ~prv:true true ss qid in
          (_Symb s (Unary(op)), s.sym_impl)
        in
        add_impl env t.pos s impl [t]
    | (P_BinO(l,b,r)  , _                 ) ->
        let (s, impl) =
          let (op,_,_,qid) = b in
          let (s, _) = find_sym ~prt:true ~prv:true true ss qid in
          (_Symb s (Binary(op)), s.sym_impl)
        in
        add_impl env t.pos s impl [l; r]
    | (P_Wrap(t)      , _                 ) -> scope env t
    | (P_Expl(_)      , _                 ) ->
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
  let m = Pervasives.ref StrMap.empty in
  Bindlib.unbox (scope (M_Term(m, expo)) ss env t)

(** [patt_vars t] returns a couple [(pvs,nl)]. The first compoment [pvs] is an
    association list giving the arity of all the “pattern variables” appearing
    in the parser-level term [t]. The second component [nl] contains the names
    of the “pattern variables” that appear non-linearly.  If a given  “pattern
    variable” occurs with different arities the program fails gracefully. *)
let patt_vars : p_term -> (string * int) list * string list =
  let rec patt_vars acc t =
    match t.elt with
    | P_Type           -> acc
    | P_Iden(_)        -> acc
    | P_Wild           -> acc
    | P_Meta(_,ts)     -> Array.fold_left patt_vars acc ts
    | P_Patt(id,ts)    -> add_patt (Array.fold_left patt_vars acc ts) id ts
    | P_Appl(t,u)      -> patt_vars (patt_vars acc t) u
    | P_Impl(a,b)      -> patt_vars (patt_vars acc a) b
    | P_Abst(xs,t)     -> patt_vars (arg_patt_vars acc xs) t
    | P_Prod(xs,b)     -> patt_vars (arg_patt_vars acc xs) b
    | P_LLet(_,xs,t,u) -> patt_vars (patt_vars (arg_patt_vars acc xs) t) u
    | P_NLit(_)        -> acc
    | P_UnaO(_,t)      -> patt_vars acc t
    | P_BinO(t,_,u)    -> patt_vars (patt_vars acc t) u
    | P_Wrap(t)        -> patt_vars acc t
    | P_Expl(t)        -> patt_vars acc t
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

(** [scope_rule ss r] turns a parser-level rewriting rule [r] into a rewriting
    rule (and the associated head symbol). *)
let scope_rule : sig_state -> p_rule -> sym * pp_hint * rule loc = fun ss r ->
  let (p_lhs, p_rhs) = r.elt in
  (* Compute the set of pattern variables on both sides. *)
  let (pvs_lhs, nl) = patt_vars p_lhs in
  let (pvs_rhs, _ ) = patt_vars p_rhs in
  (* NOTE to reject non-left-linear rules, we can check [nl = []] here. *)
  (* Check that the meta-variables of the RHS exist in the LHS. *)
  let check_in_lhs (m,i) =
    let j =
      try List.assoc m pvs_lhs with Not_found ->
      fatal p_rhs.pos "Unknown pattern variable [%s]." m
    in
    if i <> j then fatal p_lhs.pos "Arity mismatch for [%s]." m
  in
  List.iter check_in_lhs pvs_rhs;
  (* Get the non-linear variables not in the RHS. *)
  let nl = List.filter (fun m -> not (List.mem_assoc m pvs_rhs)) nl in
  (* Reserve space for meta-variables that appear non-linearly in the LHS. *)
  let pvs = List.map (fun m -> (m, List.assoc m pvs_lhs)) nl @ pvs_rhs in
  let map = List.mapi (fun i (m,_) -> (m,i)) pvs in
  (* NOTE [map] maps meta-variables to their position in the environment. *)
  (* NOTE meta-variables not in [map] can be considered as wildcards. *)
  (* Get privacy of the head of the rule, and scope the rest with this
     privacy. *)
  let prv = is_private (fst (get_root p_lhs ss)) in
  (* We scope the LHS and add indexes in the environment for metavariables. *)
  let lhs = Bindlib.unbox (scope (M_LHS(map, prv)) ss Env.empty p_lhs) in
  let (sym, hint, lhs) =
    let (h, args) = Basics.get_args lhs in
    match h with
    | Symb(s,_) when is_constant s                  ->
        fatal p_lhs.pos "Constant LHS head symbol."
    | Symb(({sym_expo=Protec; sym_path; _} as s),h) ->
        if ss.signature.sign_path <> sym_path then
          fatal p_lhs.pos "Cannot define rules on foreign protected symbols."
        else (s, h, args)
    | Symb(s,h)                                     -> (s, h, args)
    | _                                             ->
        fatal p_lhs.pos "No head symbol in LHS."
  in
  if lhs = [] then wrn p_lhs.pos "LHS head symbol with no argument.";
  (* We scope the RHS and bind the meta-variables. *)
  let names = Array.of_list (List.map fst map) in
  let vars = Bindlib.new_mvar te_mkfree names in
  let rhs =
    let map = Array.map2 (fun n v -> (n,v)) names vars in
    let mode = M_RHS(Array.to_list map, is_private sym) in
    Bindlib.unbox (Bindlib.bind_mvar vars (scope mode ss Env.empty p_rhs))
  in
  (* We also store [pvs] to facilitate confluence / termination checking. *)
  let vars = Array.of_list pvs in
  (* We put everything together to build the rule. *)
  (sym, hint, Pos.make r.pos {lhs; rhs; arity = List.length lhs; vars})

(** [scope_hint ss h] transforms a parser-level hint [h] into a rewriting rule
    defined on {!val:Sign.hint_unif}. A unification hint can be seen as a
    rewriting rule that rewrite a unification problem into several smaller
    ones. Unlike rewriting rules, unification hints may generate new
    metavariables. TODO: handle new variables generation. *)
let scope_hint : sig_state -> p_hint -> rule loc = fun ss h ->
  let (p_l, p_rs) = h.elt in
  (* Get pattern variables of [l] and [r] and verify that they are
     algebraic. *)
  let alg_patt_vars (l,r) =
    let (pvs_l, nl) = patt_vars l in
    if nl <> [] then fatal h.pos "Algebraic unification hints only.";
    let (pvs_r, nl) = patt_vars r in
    if nl <> [] then fatal h.pos "Algebraic unification hints only.";
    pvs_l @ pvs_r
  in
  (* Compute the pattern variables. *)
  let pvs =
    let pvs_lhs = alg_patt_vars p_l in
    let pvs_rhs = List.concat (List.map alg_patt_vars p_rs) in
    List.map (fun m -> (m, List.assoc m pvs_lhs)) [] @ pvs_rhs in
  (* Mapping from pattern variable names to position in environment. *)
  let map = List.mapi (fun i (m,_) -> (m,i)) pvs in
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
  let mk_unif_pb (l,r) = add_args Sign.Unif_hints.p_atom [l; r] in
  let lhs =
    let lhs =
      let p_lhs = mk_unif_pb p_l in
      Bindlib.unbox (scope (M_LHS(map, true)) ss Env.empty p_lhs)
    in
    let (h, args) = Basics.get_args lhs in
    assert (match h with Symb(s,_) -> s == Sign.Unif_hints.atom | _ -> false);
    args
  in
  (* The rhs is of the form
     - either [x ≡ t], or
     - [x ≡ t, y ≡ u, ...]
     where [x] and [y] are pattern variables. *)
  let rhs : (term_env, term) Bindlib.mbinder =
    let names = Array.of_list (List.map fst map) in
    let vars = Bindlib.new_mvar te_mkfree names in
    let rhs =
      let unif_probs = List.map mk_unif_pb p_rs in
      let p_rhs = add_args Sign.Unif_hints.p_list unif_probs in
      let map = Array.map2 (fun n v -> (n,v)) names vars in
      let mode = M_RHS(Array.to_list map, true) in
      scope mode ss Env.empty p_rhs
    in
    Bindlib.unbox (Bindlib.bind_mvar vars rhs)
  in
  let vars, rhst = Bindlib.unmbind rhs in
  (* Returns the list of bindings of the rhs as a list of [[(tevar,term)]] *)
  let rec get_bindings t =
    match Basics.get_args t with
    | Symb(h, _), [TEnv(TE_Vari(x), _); u] when h == Sign.Unif_hints.atom ->
        [(x,u)]
    | Symb(h, _), args                     when h == Sign.Unif_hints.list ->
        List.concat (List.map get_bindings args)
    | _ -> assert false (* ill formed unification hint *)
  in
  let bindings = get_bindings rhst in
  (* Ensure that pattern is linear. *)
  let eq_fst (x,_) (y,_) = Bindlib.eq_vars x y in
  if not (List.are_distinct ~eq:eq_fst bindings) then
    fatal h.pos "Only linear hint RHS allowed";
  (* Ensure that in RHS of the form [x ≡ t], [t] does not depend on [x] (and
     other variables of the hint). *)
  (* [vars_closed (_,t)] raises an error if [t] depends on a variable in
     [vars]. *)
  let vars_closed (_,t) =
    let tb = lift t in
    if Array.exists (fun x -> Bindlib.occur x tb) vars then
      fatal h.pos "RHS of sub-unification problems can't depend on patterns"
  in
  List.iter vars_closed bindings;
  (* TODO: check that unification hint is acceptable, that is, considering the
     hint [t ≡ u → x ≡ t', y ≡ u'],
     - {x, y} ⊆ FV(t) ∪ FV(u) and,
     - x and y are distinct,                  OK
     - t' and u' do not depend on x nor y,
     - t[x ≔ t', y ≔ u'] ≡ u[x ≔ t', y ≔ u']. *)
  Pos.make h.pos {lhs; rhs; arity = List.length lhs; vars = Array.of_list pvs}

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
