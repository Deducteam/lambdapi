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

(** [find_sym b st qid] returns the symbol and printing hint corresponding  to
    the qualified identifier [qid].  If [fst qid.elt] is empty,  we search for
    the name [snd qid.elt] in the opened modules of [st]. The boolean [b] only
    indicates if the error message should mention variables, in the case where
    the module path is empty and the symbol is unbound. This is reported using
    the [Fatal] exception. *)
let find_sym : bool -> sig_state -> qident -> sym * pp_hint = fun b st qid ->
  let {elt = (mp, s); pos} = qid in
  match mp with
  | []                               -> (* Symbol in scope. *)
      begin
        try (fst (StrMap.find s st.in_scope), Nothing) with Not_found ->
        let txt = if b then " or variable" else "" in
        fatal pos "Unbound symbol%s [%s]." txt s
      end
  | [m] when StrMap.mem m st.aliases -> (* Aliased module path. *)
      begin
        (* The signature must be loaded (alias is mapped). *)
        let sign =
          try PathMap.find (StrMap.find m st.aliases) Timed.(!Sign.loaded)
          with _ -> assert false (* cannot fail. *)
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

(** [find_qid st env qid] returns a boxed term corresponding to a variable  of
    the environment [env] (or to a symbol) which name corresponds to [qid]. In
    the case where the module path [fst qid.elt] is empty, we first search for
    the name [snd qid.elt] in the environment, and if it is not mapped we also
    search in the opened modules.  The exception [Fatal] is raised if an error
    occurs (e.g., when the name cannot be found). *)
let find_qid : sig_state -> env -> qident -> tbox = fun st env qid ->
  let (mp, s) = qid.elt in
  (* Check for variables in the environment first. *)
  try
    if mp <> [] then raise Not_found; (* Variables cannot be qualified. *)
    _Vari (Env.find s env)
  with Not_found ->
  (* Check for symbols. *)
  let (s, hint) = find_sym true st qid in _Symb s hint

(** Map of metavariables. *)
type metamap = meta StrMap.t

(** Representation of the different scoping modes.  Note that the constructors
    hold specific information for the given mode. *)
type mode =
  | M_Term of metamap Pervasives.ref
  (** Standard scoping mode for terms,  holding a map of metavariables
      that can be updated with new metavariables on scoping. *)
  | M_Patt
  (** Scoping mode for patterns in the rewrite tactic. *)
  | M_LHS  of (string * int) list
  (** Scoping mode for rewriting rule left-hand sides. The constructor
      carries a map associating an index to every free variable. *)
  | M_RHS  of (string * tevar) list
  (** Scoping mode for rewriting rule righ-hand sides. The constructor
      carries the environment for variables that will be bound in the
      representation of the RHS. *)

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

(** [scope md ss env t] turns a parser-level term [t] into an actual term. The
    variables of the environment [env] may appear in [t], and the scoping mode
    [md] changes the behaviour related to certain constructors.  The signature
    state [ss] is used to hande module aliasing according to [find_qid]. *)
let scope : mode -> sig_state -> env -> p_term -> tbox = fun md ss env t ->
  (* Unique pattern variable generation for wildcards in a LHS. *)
  let fresh_patt : env -> tbox =
    let c = Pervasives.ref (-1) in
    fun env ->
      let open Pervasives in
      let name = incr c; Printf.sprintf "#%i" !c in
      _Patt None name (Env.to_tbox env)
  in
  (* Toplevel scoping function, with handling of implicit arguments. *)
  let rec scope : env -> p_term -> tbox = fun env t ->
    (* Extract the spine. *)
    let (h, args) = Syntax.get_args t in
    (* Check whether application is marked as explicit in the head symbol. *)
    let expl = match h.elt with P_Iden(_,b) -> b | _ -> false in
    (* Scope the head and obtain the implicitness of arguments. *)
    let h = scope_head env h in
    let impl =
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
  and scope_domain : popt -> env -> p_term option -> tbox = fun pos env a ->
    match (a, md) with
    | (Some(a), M_LHS(_)) -> fatal a.pos "Annotation not allowed in a LHS."
    | (None   , M_LHS(_)) -> fresh_patt env
    | (None   , M_RHS(_)) -> fatal pos "Missing type annotation in a RHS."
    | (Some(a), _       ) -> scope env a
    | (None   , _       ) ->
       (* We create a new metavariable [m] of type [TYPE] for the missing
          domain. *)
       let vs = Env.to_tbox env in
       let m = fresh_meta (Env.to_prod env _Type) (Array.length vs) in
       _Meta m vs
  (* Scoping of a binder (abstraction or product). *)
  and scope_binder cons env xs t =
    let rec aux env xs =
      match xs with
      | []                  -> scope env t
      | ([]       ,_,_)::xs -> aux env xs
      | (None  ::l,d,i)::xs ->
          let v = Bindlib.new_var mkfree "_" in
          let a = scope_domain None env d in (* FIXME *)
          let t = aux env ((l,d,i)::xs) in
          cons a (Bindlib.bind_var v t)
      | (Some x::l,d,i)::xs ->
          let v = Bindlib.new_var mkfree x.elt in
          let a = scope_domain x.pos env d in
          let env = if x.elt = "_" then env else (x.elt,(v,a))::env in
          let t = aux env ((l,d,i)::xs) in
          cons a (Bindlib.bind_var v t)
    in
    aux env xs
  (* Scoping function for head terms. *)
  and scope_head : env -> p_term -> tbox = fun env t ->
    match (t.elt, md) with
    | (P_Type          , M_LHS(_) ) -> fatal t.pos "Not allowed in a LHS."
    | (P_Type          , _        ) -> _Type
    | (P_Iden(qid,_)   , _        ) -> find_qid ss env qid
    | (P_Wild          , M_RHS(_) ) -> fatal t.pos "Not allowed in a RHS."
    | (P_Wild          , M_LHS(_) ) -> fresh_patt env
    | (P_Wild          , M_Patt   ) -> _Wild
    | (P_Wild          , M_Term(_)) ->
       (* We create a new metavariable [m1] of type [TYPE] and a new
          metavariable [m2] of type [m1], and return [m2]. *)
        let vs = Env.to_tbox env in
        let m1 = fresh_meta (Env.to_prod env _Type) (Array.length vs) in
        let a = Env.to_prod env (_Meta m1 vs) in
        let m2 = fresh_meta a (Array.length vs) in
        _Meta m2 vs
    | (P_Meta(id,ts)   , M_Term(m)) ->
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
    | (P_Meta(_,_)     , _        ) -> fatal t.pos "Not allowed in a rule."
    | (P_Patt(id,ts)   , M_LHS(m) ) ->
        let i =
          try Some(List.assoc id.elt m) with Not_found ->
            if !verbose > 1 then
              wrn t.pos "Pattern variable not bound in the RHS.";
            None
        in
        (* Check that [ts] are variables. *)
        let scope_var t =
          match unfold (Bindlib.unbox (scope env t)) with
          | Vari(x) -> x
          | _       ->
             fatal t.pos "Pattern variables can be applied \
                          to distinct bound variables only."
        in
        let vs = Array.map scope_var ts in
        (* Check that [vs] are distinct variables. *)
        for i=1 to Array.length vs - 1 do
          for j=0 to i-1 do
            if Bindlib.eq_vars vs.(i) vs.(j) then
              fatal t.pos "Pattern variables can be applied \
                           to distinct bound variables only."
          done
        done;
        _Patt i id.elt (Array.map Bindlib.box_var vs)
    | (P_Patt(id,ts)   , M_RHS(m) ) ->
        let x =
          try List.assoc id.elt m with Not_found ->
          fatal t.pos "Pattern variable not in scope." (* Cannot happen. *)
        in
        _TEnv (Bindlib.box_var x) (Array.map (scope env) ts)
    | (P_Patt(_,_)     , _        ) -> fatal t.pos "Only allowed in rules."
    | (P_Appl(_,_)     , _        ) -> assert false (* Unreachable. *)
    | (P_Impl(_,_)     , M_LHS(_) ) -> fatal t.pos "Not allowed in a LHS."
    | (P_Impl(_,_)     , M_Patt   ) -> fatal t.pos "Not allowed in a pattern."
    | (P_Impl(a,b)     , _        ) -> _Impl (scope env a) (scope env b)
    | (P_Abst(_,_)     , M_Patt   ) -> fatal t.pos "Not allowed in a pattern."
    | (P_Abst(xs,t)    , _        ) -> scope_binder _Abst env xs t
    | (P_Prod(_,_)     , M_LHS(_) ) -> fatal t.pos "Not allowed in a LHS."
    | (P_Prod(_,_)     , M_Patt   ) -> fatal t.pos "Not allowed in a pattern."
    | (P_Prod(xs,b)    , _        ) -> scope_binder _Prod env xs b
    | (P_LLet(x,xs,t,u), M_Term(_)) ->
        (* “let x = t in u” is desugared as “(λx.u) t” (for now). *)
        let t = scope env (if xs = [] then t else Pos.none (P_Abst(xs,t))) in
        _Appl (scope env (Pos.none (P_Abst([([Some x],None,false)], u)))) t
    | (P_LLet(_,_,_,_) , _        ) -> fatal t.pos "Only allowed in terms."
    | (P_NLit(n)       , _        ) ->
        let sym_z = _Symb (Sign.builtin t.pos ss.builtins "0") Nothing
        and sym_s = _Symb (Sign.builtin t.pos ss.builtins "+1") Nothing in
        let rec unsugar_nat_lit acc n =
          if n <= 0 then acc else unsugar_nat_lit (_Appl sym_s acc) (n-1)
        in
        unsugar_nat_lit sym_z n
    | (P_BinO(l,b,r)  , _         ) ->
        let (s, impl) =
          let (op,_,_,qid) = b in
          let (s, _) = find_sym true ss qid in
          (_Symb s (Binary(op)), s.sym_impl)
        in
        add_impl env t.pos s impl [l; r]
    | (P_Wrap(t)      , _         ) -> scope env t
    | (P_Expl(_)      , _         ) ->
        fatal t.pos "Explicit argument not allowed here."
  in
  scope env t

(** [scope md ss env t] turns a parser-level term [t] into an actual term. The
    variables of the environment [env] may appear in [t], and the scoping mode
    [md] changes the behaviour related to certain constructors.  The signature
    state [ss] is used to hande module aliasing according to [find_qid]. *)
let scope_term : metamap -> sig_state -> env -> p_term -> term * metamap
  = fun m ss env t ->
  let m = Pervasives.ref m in
  let t = scope (M_Term(m)) ss env t in
  (Bindlib.unbox t, Pervasives.(!m))

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
    | P_Patt(id,ts)    ->
        let (pvs, nl) as acc = Array.fold_left patt_vars acc ts in
        let l = Array.length ts in
        begin
          try
            if List.assoc id.elt pvs <> l then
              fatal id.pos "Arity mismatch for pattern variable [%s]." id.elt;
            if List.mem id.elt nl then acc else (pvs, id.elt::nl)
          with Not_found -> ((id.elt,l)::pvs, nl)
        end
    | P_Appl(t,u)      -> patt_vars (patt_vars acc t) u
    | P_Impl(a,b)      -> patt_vars (patt_vars acc a) b
    | P_Abst(xs,t)     -> patt_vars (arg_patt_vars acc xs) t
    | P_Prod(xs,b)     -> patt_vars (arg_patt_vars acc xs) b
    | P_LLet(_,xs,t,u) -> patt_vars (patt_vars (arg_patt_vars acc xs) t) u
    | P_NLit(_)        -> acc
    | P_BinO(t,_,u)    -> patt_vars (patt_vars acc t) u
    | P_Wrap(t)        -> patt_vars acc t
    | P_Expl(t)        -> patt_vars acc t
  and arg_patt_vars acc xs =
    match xs with
    | []                       -> acc
    | (_, None,    _   ) :: xs -> arg_patt_vars acc xs
    | (_, Some(a), _) :: xs    -> arg_patt_vars (patt_vars acc a) xs
  in patt_vars ([],[])

(** [scope_rule ss r] turns a parser-level rewriting rule [r] into a rewriting
    rule (and the associated head symbol). *)
let scope_rule : sig_state -> p_rule -> sym * pp_hint * rule loc = fun ss r ->
  let (p_lhs, p_rhs) = r.elt in
  (* Compute the set of pattern variables on both sides. *)
  let (pvs_lhs, nl) = patt_vars p_lhs in
  let (pvs    , _ ) = patt_vars p_rhs in
  (* NOTE to reject non-left-linear rules, we can check [nl = []] here. *)
  (* Check that the meta-variables of the RHS exist in the LHS. *)
  let check_in_lhs (m,i) =
    let j =
      try List.assoc m pvs_lhs with Not_found ->
      fatal p_rhs.pos "Unknown pattern variable [%s]." m
    in
    if i <> j then fatal p_lhs.pos "Arity mismatch for [%s]." m
  in
  List.iter check_in_lhs pvs;
  (* Get the non-linear variables not in the RHS. *)
  let nl = List.filter (fun m -> not (List.mem_assoc m pvs)) nl in
  (* Reserve space for meta-variables that appear non-linearly in the LHS. *)
  let pvs = pvs @ (List.map (fun m -> (m, List.assoc m pvs_lhs)) nl) in
  let map = List.mapi (fun i (m,_) -> (m,i)) pvs in
  (* NOTE [map] maps meta-variables to their position in the environment. *)
  (* NOTE meta-variables not in [map] can be considered as wildcards. *)
  (* We scope the LHS and add indexes in the environment for metavariables. *)
  let lhs = Bindlib.unbox (scope (M_LHS(map)) ss Env.empty p_lhs) in
  let (sym, hint, lhs) =
    let (h, args) = Basics.get_args lhs in
    let is_const s = s.sym_mode = Const in
    match h with
    | Symb(s,_) when is_const s -> fatal p_lhs.pos "Constant LHS head symbol."
    | Symb(s,h)                 -> (s, h, args)
    | _                         -> fatal p_lhs.pos "No head symbol in LHS."
  in
  if lhs = [] && !verbose > 1 then
    wrn p_lhs.pos "LHS head symbol with no argument.";
  (* We scope the RHS and bind the meta-variables. *)
  let names = Array.of_list (List.map fst map) in
  let vars = Bindlib.new_mvar te_mkfree names in
  let rhs =
    let map = Array.map2 (fun n v -> (n,v)) names vars in
    let t = scope (M_RHS(Array.to_list map)) ss Env.empty p_rhs in
    Bindlib.unbox (Bindlib.bind_mvar vars t)
  in
  (* We also store [pvs] to facilitate confluence / termination checking. *)
  let vars = Array.of_list pvs in
  (* We put everything together to build the rule. *)
  (sym, hint, Pos.make r.pos {lhs; rhs; arity = List.length lhs; vars})

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
