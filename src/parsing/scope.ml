(** Scoping. *)

open! Lplib
open Common
open Error
open Pos
open Syntax
open Core
open Term
open Env
open Sig_state
open Debug

(** Logging function for term scoping. *)
let log_scop = new_logger 'o' "scop" "term scoping"
let log_scop = log_scop.logger

(** [find_qid prt prv ss env qid] returns a boxed term corresponding to a
   variable of the environment [env] (or to a symbol) which name corresponds
   to [qid]. In the case where the module path [fst qid.elt] is empty, we
   first search for the name [snd qid.elt] in the environment, and if it is
   not mapped we also search in the opened modules. The exception [Fatal] is
   raised if an error occurs (e.g., when the name cannot be found). If [prt]
   is true, protected symbols from external modules are allowed (protected
   symbols from current modules are always allowed). If [prv] is true, private
   symbols are allowed. *)
let find_qid : bool -> bool -> sig_state -> env -> p_qident -> tbox =
  fun prt prv ss env qid ->
  if Timed.(!log_enabled) then log_scop "find_qid %a" Pretty.qident qid;
  let (mp, s) = qid.elt in
  (* Check for variables in the environment first. *)
  try
    if mp <> [] then raise Not_found; (* Variables cannot be qualified. *)
    _Vari (Env.find s env)
  with Not_found ->
    (* Check for symbols. *)
    _Symb (find_sym ~prt ~prv ss qid)

(** [get_root ss env t] returns the symbol at the root of the term [t]. *)
let get_root : sig_state -> Env.t -> p_term -> sym = fun ss env t ->
  let rec get_root t =
    match t.elt with
    | P_Iden(qid,_) -> find_sym ~prt:true ~prv:true ss qid
    | P_Appl(t, _)  -> get_root t
    | P_Wrap(t)     -> get_root (Pratt.parse ss env t)
    | _             -> assert false
  in
  (* Pratt parse to order terms correctly. *)
  get_root (Pratt.parse ss env t)

(** Representation of the different scoping modes.  Note that the constructors
    hold specific information for the given mode. *)
type lhs_data =
  { m_lhs_prv              : bool
  (** True if private symbols are allowed. *)
  ; m_lhs_indices          : (string, int   ) Hashtbl.t
  (** Stores index reserved for a pattern variable of the given name. *)
  ; m_lhs_arities          : (int   , int   ) Hashtbl.t
  (** Stores the arity of the pattern variable at the given index. *)
  ; m_lhs_names            : (int   , string) Hashtbl.t
  (** Stores the name of the pattern variable at given index (if any). *)
  ; mutable m_lhs_size     : int
  (** Stores the current known size of the environment of the RHS. *)
  ; m_lhs_in_env           : string list
  (** Pattern variables definitely needed in the RHS environment. *) }

type mode =
  | M_Term of
      { mutable m_term_new_metas : problem
      (** Metavariables generated during scoping. *)
      ; m_term_meta_of_name : string -> meta option
      (** Returns the meta with the given name. *)
      ; m_term_meta_of_key : int -> meta option
      (** Returns the meta with the give key. *)
      ; m_term_prv : bool
      (** Indicate if private symbols are allowed. *) }
  (** Standard scoping mode for terms, holding a map for metavariables
     introduced by the user, a map for metavariables generated by the system,
     and a boolean indicating whether private symbols are allowed. *)
  | M_Patt
  (** Scoping mode for patterns in the rewrite tactic. *)
  | M_LHS of lhs_data
  (** Scoping mode for rewriting rule left-hand sides. *)
  | M_RHS of
      { m_rhs_prv  : bool
      (** True if private symbols are allowed. *)
      ; m_rhs_data : (string, tevar) Hashtbl.t
      (** Environment for variables that we know to be bound in the RHS. *)
      ; mutable m_rhs_new_metas : problem
      (** Metavariables generated during scoping. *) }
  (** Scoping mode for rewriting rule right-hand sides. *)
  | M_URHS of
      { mutable m_urhs_vars_nb : int
      (** Number  of  distinct  variables  in  the rewriting  rule,  including
          variables  only in  the  RHS. It  is initialised  to  the number  of
          (distinct) variables in the LHS and incremented each time a variable
          of the RHS that was not in the LHS is scoped. *)
      ; mutable m_urhs_xvars : (string * tevar) list
      (** Variables scoped that  were not in the LHS. This  field is only used
          in  unification  rules and  is  updated  imperatively for  each  new
          variable scoped. A couple [(n, v)]  is the name of the variable with
          the variable itself. The name is needed to ensure that two variables
          with the same name are scoped as the same variable. *)
      ; m_urhs_data : (string, tevar) Hashtbl.t }
  (** Scoping mode for unification rule right-hand sides. During  scoping, we
      always have [m_urhs_vars_nb = m_lhs_size + length m_urhs_xvars]. *)

(** [fresh_patt name ts] creates a unique pattern variable applied to
   [ts]. [name] is used as suffix if distinct from [None]. *)
let fresh_patt : lhs_data -> string option -> tbox array -> tbox =
  fun data nopt ts ->
  let fresh_index () =
    let i = data.m_lhs_size in
    data.m_lhs_size <- i + 1;
    let arity = Array.length ts in
    Hashtbl.add data.m_lhs_arities i arity; i
  in
  match nopt with
  | Some name ->
      let i =
        try Hashtbl.find data.m_lhs_indices name with Not_found ->
          let i = fresh_index () in
          Hashtbl.add data.m_lhs_indices name i;
          Hashtbl.add data.m_lhs_names i name; i
      in
      _Patt (Some i) (Escape.add_suffix (Printf.sprintf "v%i_" i) name) ts
  | None ->
      let i = fresh_index () in
      _Patt (Some i) (Printf.sprintf "v%i" i) ts

(** [fresh_meta_type md env] calls [Env.fresh_meta_type] and updates the set
   of new metavariables in [md]. *)
let fresh_meta_type : mode -> env -> tbox = fun md env ->
  match md with
  | M_Term d -> Env.fresh_meta_type d.m_term_new_metas env
  | M_RHS d -> Env.fresh_meta_type d.m_rhs_new_metas env
  | _ -> assert false

(** [fresh_meta_tbox md env] calls [Env.fresh_meta_tbox] and updates the set
   of new metavariables in [md]. *)
let fresh_meta_tbox : mode -> env -> tbox = fun md env ->
  match md with
  | M_Term d -> Env.fresh_meta_tbox d.m_term_new_metas env
  | M_RHS d -> Env.fresh_meta_tbox d.m_rhs_new_metas env
  | _ -> assert false

(** [scope md ss env t] turns a parser-level term [t] into an actual term. The
   variables of the environment [env] may appear in [t], and the scoping mode
   [md] changes the behaviour related to certain constructors. The signature
   state [ss] is used to convert identifiers into symbols according to
   [find_qid]. *)
let rec scope : mode -> sig_state -> env -> p_term -> tbox =
  fun md ss env t -> scope_parsed md ss env (Pratt.parse ss env t)
(** [scope_parsed md ss env t] turns a parser-level, Pratt-parsed term [t]
   into an actual term. *)
and scope_parsed : mode -> sig_state -> env -> p_term -> tbox =
  fun md ss env t ->
  if Timed.(!log_enabled) then log_scop "%a" Pretty.term t;
  (* Extract the spine. *)
  let p_head, args = Syntax.p_get_args t in
  (* Check that LHS pattern variables are applied to no argument. *)
  begin
    match p_head.elt, md with
    | P_Patt _, M_LHS _ when args <> [] ->
      fatal t.pos "Pattern variables cannot be applied."
    | _ -> ()
  end;
  (* Scope the head and obtain the implicitness of arguments. *)
  let h = scope_head md ss env p_head in
  (* Find out whether [h] has implicit arguments. *)
  let impl =
    match p_head.elt with
    | P_Iden (_, false)
    | P_Wrap ({ elt = P_Iden (_, false); _ }) ->
        (* We avoid unboxing if [h] is not closed (and hence not a symbol). *)
        if Bindlib.is_closed h then
          match Bindlib.unbox h with
          | Symb s -> s.sym_impl
          | _ -> []
        else []
    | _ -> []
  in
  (* Scope and insert the (implicit) arguments. *)
  add_impl md ss env t.pos h impl args

(** [add_impl md ss env loc h impl args] scopes [args] and returns the
   application of [h] to the scoped arguments. [impl] is a boolean list
   described the implicit arguments. Implicit arguments are added as
   underscores before scoping. *)
and add_impl : mode -> sig_state ->
               Env.t -> popt -> tbox -> bool list -> p_term list -> tbox =
  fun md ss env loc h impl args ->
  let appl = match md with M_LHS _ -> _Appl_not_canonical | _ -> _Appl in
  let appl_p_term t u = appl t (scope_parsed md ss env u) in
  let appl_meta t = appl t (scope_head md ss env P.wild) in
  match (impl, args) with
  (* The remaining arguments are all explicit. *)
  | ([]         , _      ) -> List.fold_left appl_p_term h args
  (* Only implicit arguments remain. *)
  | (true ::impl, []     ) -> add_impl md ss env loc (appl_meta h) impl []
  (* The first argument is implicit (could be [a] if made explicit). *)
  | (true ::impl, a::args) ->
      begin
        match a.elt with
        | P_Expl b ->
            add_impl md ss env loc
              (appl_p_term h {a with elt = P_Wrap b}) impl args
        | _ -> add_impl md ss env loc (appl_meta h) impl (a::args)
      end
  (* The first argument [a] is explicit. *)
  | (false::impl, a::args) ->
      begin
        match a.elt with
        | P_Expl _ -> fatal a.pos "Unexpected explicit argument."
        | _        -> add_impl md ss env loc (appl_p_term h a) impl args
      end
  (* The application is too "partial" to insert all implicit arguments. *)
  | (false::_   , []     ) ->
      (* NOTE this could be improved with more general implicits. *)
      fatal loc "More arguments are required to instantiate implicits."

(** [scope_domain md ss env t] scopes [t] as the domain of an abstraction or
   product. *)
and scope_domain : mode -> sig_state -> env -> p_term option -> tbox =
  fun md ss env a ->
  match a, md with
  | (Some {elt=P_Wild;_}|None), M_LHS data ->
      fresh_patt data None (Env.to_tbox env)
  | (Some {elt=P_Wild;_}|None), _ -> fresh_meta_type md env
  | Some a, _ -> scope md ss env a

(** [scope_binder ?warn mode ss cons env params_list t] scopes [t] in mode
   [md], signature state [ss] and environment [env]. [params_list] is a list
   of paramters to abstract on. For each parameter, a tbox is built using
   [cons] (either [_Abst] or [_Prod]). If [?warn] is true (the default), a
   warning is printed when the variable that is bound by the binder does not
   appear in the body. *)
and scope_binder : ?warn:bool -> mode -> sig_state ->
  (tbox -> tbinder Bindlib.box -> tbox) -> Env.t -> p_params list ->
  p_term option -> tbox =
  fun ?(warn=true) md ss cons env params_list t ->
  let rec scope_params_list env params_list =
    match params_list with
    | [] ->
        begin
          match t with
          | Some t -> scope md ss env t
          | None -> fresh_meta_type md env
        end
    | (idopts,typopt,_implicit)::params_list ->
        scope_params env idopts (scope_domain md ss env typopt) params_list
  and scope_params env idopts a params_list =
    let rec aux env idopts =
      match idopts with
      | [] -> scope_params_list env params_list
      | None::idopts ->
          let v = new_tvar "_" in
          let t = aux env idopts in
          cons a (Bindlib.bind_var v t)
      | Some {elt=id;pos}::idopts ->
          if LpLexer.is_invalid_bindlib_id id then
            fatal pos "Escaped identifiers or regular identifiers with an \
                       integer suffix with leading zeros are not allowed \
                       for bound variable names.";
          let v = new_tvar id in
          let env = Env.add v a None env in
          let t = aux env idopts in
          if warn && id.[0] <> '_' && not (Bindlib.occur v t) then
            wrn pos "Variable %s could be replaced by '_'." id;
          cons a (Bindlib.bind_var v t)
    in aux env idopts
  in
  scope_params_list env params_list

(** [scope_head md ss env t] scopes [t] as term head. *)
and scope_head : mode -> sig_state -> env -> p_term -> tbox =
  fun md ss env t ->
  match (t.elt, md) with
  | (P_Type, M_LHS(_)) -> fatal t.pos "TYPE is not allowed in a LHS."
  | (P_Type, _) -> _Type

  | (P_Iden(qid,_), M_LHS(d)) -> find_qid true d.m_lhs_prv ss env qid
  | (P_Iden(qid,_), M_Term{m_term_prv=true;_}) ->
      find_qid false true ss env qid
  | (P_Iden(qid,_), M_RHS(d)) -> find_qid false d.m_rhs_prv ss env qid
  | (P_Iden(qid,_), _) -> find_qid false false ss env qid

  | (P_Wild, M_URHS(data)) ->
    let x =
      let name = Printf.sprintf "v%i" data.m_urhs_vars_nb in
      let x = new_tevar name in
      data.m_urhs_vars_nb <- data.m_urhs_vars_nb + 1;
      data.m_urhs_xvars <- (name, x) :: data.m_urhs_xvars;
      x
    in
    _TEnv (_TE_Vari x) (Env.to_tbox env)
  | (P_Wild, M_LHS data) -> fresh_patt data None (Env.to_tbox env)
  | (P_Wild, M_Patt) -> _Wild
  | (P_Wild, (M_RHS _|M_Term _)) -> fresh_meta_tbox md env

  | (P_Meta({elt;pos},ts), M_Term d) ->
      let m =
        match elt with
        | Name id ->
            begin
              match d.m_term_meta_of_name id with
              | Some m -> m
              | None ->
              match LibMeta.of_name id d.m_term_new_metas with
              | Some m -> m
              | None ->
               (* We create a new metavariable [m1] of type [TYPE] and a new
                  metavariable [m] of name [id] and type [m1]. *)
                  let vs = Env.to_tbox env in
                  let arity = Array.length vs in
                  let m1 =
                    LibMeta.fresh d.m_term_new_metas
                      (Env.to_prod env _Type) arity in
                  let a = Env.to_prod env (_Meta m1 vs) in
                  LibMeta.fresh d.m_term_new_metas ~name:id a arity
             end
        | Numb i ->
            match d.m_term_meta_of_key i with
            | Some m -> m
            | None -> fatal pos "Unknown metavariable ?%d." i
      in
      let ts =
        match ts with
        | None -> Env.to_tbox env (* [?M] is equivalent to [?M[env]]. *)
        | Some ts -> Array.map (scope md ss env) ts
      in
      _Meta m ts
  | (P_Meta(_,_), _) -> fatal t.pos "Metavariables are not allowed here."

  | (P_Patt(id,ts), M_LHS(d)) ->
      (* Check that [ts] are variables. *)
      let scope_var t =
        match unfold (Bindlib.unbox (scope md ss env t)) with
        | Vari(x) -> x
        | _       -> fatal t.pos "Only bound variables are allowed in the \
                                  environment of pattern variables."
      in
      let ts =
        match ts with
        | None ->
            if env = [] then [||] (* $M stands for $M[] *)
            else fatal t.pos "Missing square brackets under binder."
        | Some ts ->
            let vs = Array.map scope_var ts in
            (* Check that [vs] are distinct variables. *)
            for i = 0 to Array.length vs - 2 do
              for j = i + 1 to Array.length vs - 1 do
                if Bindlib.eq_vars vs.(i) vs.(j) then
                  fatal ts.(j).pos
                    "Variable %a appears more than once \
                     in the environment of a pattern variable."
                    Print.pp_var vs.(j)
              done
            done;
            Array.map _Vari vs
      in
      begin
        match id with
        | None when List.length env = Array.length ts ->
            wrn t.pos
              "Pattern [%a] could be replaced by [_]." Pretty.term t;
        | Some {elt=id;pos} when not (List.mem id d.m_lhs_in_env) ->
            if List.length env = Array.length ts then
              wrn pos "Pattern variable %s can be replaced by a '_'." id
            else wrn pos "Pattern variable %s doesn't need to be named." id
        | _ -> ()
      end;
      fresh_patt d (Option.map (fun id -> id.elt) id) ts
  | (P_Patt(id,ts), M_URHS(r)) ->
      let x =
        match id with
        | None     -> fatal t.pos "Wildcard pattern not allowed in a URHS."
        | Some {elt=id;_} ->
            (* Search in variables declared in LHS. *)
            try Hashtbl.find r.m_urhs_data id
            with Not_found ->
              (* Search in variables already declared in RHS. *)
              try List.assoc id r.m_urhs_xvars
              with Not_found ->
                let name = Escape.add_suffix
                             (Printf.sprintf "v%i_" r.m_urhs_vars_nb) id
                in
                let x = new_tevar name in
                r.m_urhs_vars_nb <- r.m_urhs_vars_nb + 1;
                r.m_urhs_xvars   <- (id, x) :: r.m_urhs_xvars;
                x
      in
      let ts =
        match ts with
        | None -> [||] (* $M stands for $M[] *)
        | Some ts -> Array.map (scope md ss env) ts
      in
      _TEnv (_TE_Vari x) ts
  | (P_Patt(id,ts), M_RHS(r)) ->
      let x =
        match id with
        | None     -> fatal t.pos "Wildcard pattern not allowed in a RHS."
        | Some(id) ->
            (* Search in variables declared in LHS. *)
            try Hashtbl.find r.m_rhs_data id.elt
            with Not_found -> fatal t.pos "Variable must be in LHS."
      in
      let ts =
        match ts with
        | None -> [||] (* $M stands for $M[] *)
        | Some ts -> Array.map (scope md ss env) ts
      in
      _TEnv (_TE_Vari x) ts
  | (P_Patt(_,_), _) ->
      fatal t.pos "Pattern variables are only allowed in rewriting rules."

  | (P_Appl(_,_), _) ->  assert false (* Unreachable. *)

  | (P_Arro(_,_), M_Patt) ->
      fatal t.pos "Implications are not allowed in a pattern."
  | (P_Arro(a,b), _) -> _Impl (scope md ss env a) (scope md ss env b)

  | (P_Abst(_,_), M_Patt) ->
      fatal t.pos "Abstractions are not allowed in a pattern."
  | (P_Abst(xs,t), _) -> scope_binder md ss _Abst env xs (Some(t))

  | (P_Prod(_,_), M_Patt) ->
      fatal t.pos "Dependent products are not allowed in a pattern."
  | (P_Prod(xs,b), _) -> scope_binder md ss _Prod env xs (Some(b))

  | (P_LLet(x,xs,a,t,u), (M_Term _|M_URHS _|M_RHS _)) ->
      let a = scope_binder md ss _Prod env xs a in
      let t = scope_binder md ss _Abst env xs (Some(t)) in
      let v = new_tvar x.elt in
      let u = scope md ss (Env.add v a (Some(t)) env) u in
      if not (Bindlib.occur v u) then
        wrn x.pos "Useless let-binding (%s is not bound)." x.elt;
      _LLet a t (Bindlib.bind_var v u)
  | (P_LLet(_), M_LHS(_)) ->
      fatal t.pos "Let-bindings are not allowed in a LHS."
  | (P_LLet(_), M_Patt) ->
      fatal t.pos "Let-bindings are not allowed in a pattern."

  | (P_NLit(n), _) ->
      let sym_z = _Symb (Builtin.get ss t.pos "0")
      and sym_s = _Symb (Builtin.get ss t.pos "+1") in
      let rec unsugar_nat_lit acc n =
        if n <= 0 then acc else unsugar_nat_lit (_Appl sym_s acc) (n-1) in
      unsugar_nat_lit sym_z n

  (* Evade the addition of implicit arguments inside the wrap *)
  | (P_Wrap ({ elt = P_Iden _; _ } as id), _) -> scope_head md ss env id
  | (P_Wrap t, _) -> scope md ss env t

  | (P_Expl(_), _) -> fatal t.pos "Explicit argument not allowed here."

(** [scope expo ss env p mok mon t] turns into a term a pterm [t] in the
   signature state [ss], the environment [env] (for bound variables). [mok k]
   says if there already exists a meta with key [k]. [mon n] says if there
   already exissts a meta with name [n]. Generated metas are added to [p]. If
   [expo] is {!constructor:Public}, then the term must not contain any private
   subterms. *)
let scope_term :
      bool -> sig_state -> env
      -> problem -> (int -> meta option) -> (string -> meta option)
      -> p_term -> term =
  fun m_term_prv ss env
      m_term_new_metas m_term_meta_of_key m_term_meta_of_name t ->
  let md = M_Term {m_term_new_metas; m_term_meta_of_key;
                   m_term_meta_of_name; m_term_prv} in
  Bindlib.unbox (scope md ss env t)

(** [scope_term_with_params expo ss env p mok mon t] is similar to [scope_term
   expo ss env p mok mon t] except that [t] must be a product or an
   abstraction. In this case, no warnings are issued if the top binders are
   constant. *)
let scope_term_with_params :
      bool -> sig_state -> env
      -> problem -> (int -> meta option) -> (string -> meta option)
      -> p_term -> term =
  fun m_term_prv ss env
      m_term_new_metas m_term_meta_of_key m_term_meta_of_name t ->
  if Timed.(!log_enabled) then log_scop "%a" Pretty.term t;
  let md = M_Term {m_term_new_metas; m_term_meta_of_key;
                   m_term_meta_of_name; m_term_prv} in
  let scope_b cons xs u =
    Bindlib.unbox (scope_binder ~warn:false md ss cons env xs (Some u))
  in
  match t.elt with
  | P_Abst(xs,u) -> scope_b _Abst xs u
  | P_Prod(xs,u) -> scope_b _Prod xs u
  | _ -> assert false

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
    | P_Meta(_,None)     -> acc
    | P_Meta(_,Some ts)  -> Array.fold_left (patt_vars) acc ts
    | P_Patt(id,ts)      -> add_patt acc id ts
    | P_Appl(t,u)        -> patt_vars (patt_vars acc t) u
    | P_Arro(a,b)        -> patt_vars (patt_vars acc a) b
    | P_Abst(args,t)     -> patt_vars (patt_vars_args acc args) t
    | P_Prod(args,b)     -> patt_vars (patt_vars_args acc args) b
    | P_LLet(_,args,a,t,u) ->
        let pvs = patt_vars (patt_vars (patt_vars_args acc args) t) u in
        begin
          match a with
          | None    -> pvs
          | Some(a) -> patt_vars pvs a
        end
    | P_NLit(_)          -> acc
    | P_Wrap(t)          -> patt_vars acc t
    | P_Expl(t)          -> patt_vars acc t
  and add_patt ((pvs, nl) as acc) id ts =
    let acc, arity =
      match ts with
      | None     -> (acc, 0)
      | Some(ts) -> (Array.fold_left patt_vars acc ts, Array.length ts)
    in
    match id with
    | None     -> acc
    | Some {elt=id;pos} ->
        begin
          try
            if List.assoc id pvs <> arity then
              fatal pos "Arity mismatch for pattern variable %s." id;
            if List.mem id nl then acc else (pvs, id::nl)
          with Not_found -> ((id, arity)::pvs, nl)
        end
  and patt_vars_args acc args =
    match args with
    | []            -> acc
    | (_,a,_)::args ->
        let acc = match a with None -> acc | Some a -> patt_vars acc a in
        patt_vars_args acc args
  in
  patt_vars ([],[])

(** Representation of a rewriting rule prior to SR-checking. *)
type pre_rule =
  { pr_sym      : sym
  (** Head symbol of the LHS. *)
  ; pr_lhs      : term list
  (** Arguments of the LHS. *)
  ; pr_vars     : term_env Bindlib.mvar
  (** Pattern variables that appear in the RHS. The last [pr_xvars_nb]
      variables do not appear in the LHS. *)
  ; pr_rhs      : tbox
  (** Body of the RHS, should only be unboxed once. *)
  ; pr_names    : (int, string) Hashtbl.t
  (** Gives the original name (if any) of pattern variable at given index. *)
  ; pr_arities  : int array
  (** Gives the arity of all the pattern variables in field [pr_vars]. *)
  ; pr_xvars_nb : int
  (** Number of variables that appear in the RHS but not in the LHS. *) }

(** [rule_of_pre_rule r] converts a pre-rewrite rule into a rewrite rule. *)
let rule_of_pre_rule : pre_rule -> rule =
  fun {pr_lhs; pr_vars; pr_rhs; pr_arities; pr_xvars_nb; _} ->
  { lhs = pr_lhs
  ; rhs = Bindlib.(unbox (bind_mvar pr_vars pr_rhs))
  ; arity = List.length pr_lhs
  ; arities = pr_arities
  ; vars = pr_vars
  ; xvars_nb = pr_xvars_nb }

(** [scope_rule ur ss r] turns a parser-level rewriting rule [r], or a
    unification rule if [ur] is true, into a pre-rewriting rule. *)
let scope_rule : bool -> sig_state -> p_rule -> pre_rule loc = fun ur ss r ->
  let (p_lhs, p_rhs) = r.elt in
  (* Compute the set of pattern variables on both sides. *)
  let (pvs_lhs, nl) = patt_vars p_lhs in
  (* NOTE to reject non-left-linear rules check [nl = []] here. *)
  let (pvs_rhs, _ ) = patt_vars p_rhs in
  (* Check that pattern variables of RHS that are in the LHS have the right
     arity. *)
  let check_arity (m,i) =
    try
      let j = List.assoc m pvs_lhs in
      if i <> j then fatal p_lhs.pos "Arity mismatch for %s." m
    with Not_found -> ()
  in
  List.iter check_arity pvs_rhs;
  (* Scope the LHS and get the reserved index for named pattern variables. *)
  let (pr_lhs, lhs_indices, lhs_arities, lhs_names, lhs_size) =
    let mode =
      M_LHS{ m_lhs_prv     = is_private (get_root ss [] p_lhs)
           ; m_lhs_indices = Hashtbl.create 7
           ; m_lhs_arities = Hashtbl.create 7
           ; m_lhs_names   = Hashtbl.create 7
           ; m_lhs_size    = 0
           ; m_lhs_in_env  = nl @ List.map fst pvs_rhs }
    in
    let pr_lhs = scope mode ss Env.empty p_lhs in
    match mode with
    | M_LHS{ m_lhs_indices; m_lhs_names; m_lhs_size; m_lhs_arities; _} ->
        (Bindlib.unbox pr_lhs, m_lhs_indices, m_lhs_arities, m_lhs_names,
         m_lhs_size)
    | _                                                  -> assert false
  in
  (* Check the head symbol and build the actual LHS. *)
  let (sym, pr_lhs) =
    let (h, args) = get_args pr_lhs in
    match h with
    | Symb(s) ->
        if is_constant s then fatal p_lhs.pos "Constant LHS head symbol.";
        if s.sym_expo = Protec && ss.signature.sign_path <> s.sym_path then
          fatal p_lhs.pos "Cannot define rules on foreign protected symbols.";
        (s, args)
    | _ -> fatal p_lhs.pos "No head symbol in LHS."
  in
  (* Create the pattern variables that can be bound in the RHS. *)
  let pr_vars =
    Array.init lhs_size (fun i ->
        new_tevar
          (try Escape.add_suffix (Printf.sprintf "v%i_" i)
                 (Hashtbl.find lhs_names i)
           with Not_found -> Printf.sprintf "v%i" i))
  in
  let mode =
    let htbl_vars = Hashtbl.create (Hashtbl.length lhs_indices) in
    let fn k i = Hashtbl.add htbl_vars k pr_vars.(i) in
    Hashtbl.iter fn lhs_indices;
    if ur then
      M_URHS{ m_urhs_data = htbl_vars ; m_urhs_vars_nb = Array.length pr_vars
            ; m_urhs_xvars = [] }
    else
      M_RHS{ m_rhs_prv = is_private sym; m_rhs_data = htbl_vars;
             m_rhs_new_metas = new_problem() }
  in
  let pr_rhs = scope mode ss Env.empty p_rhs in
  let prerule =
    (* We put everything together to build the pre-rule. *)
    let pr_arities =
      let fn i =
        try Hashtbl.find lhs_arities i
        with Not_found -> assert false (* Unreachable. *)
      in
      Array.init lhs_size fn
    in
    if ur then (* Unification rule. *)
      (* We scope the RHS and retrieve variables not occurring in the LHS. *)
      let xvars =
        match mode with
        | M_URHS{m_urhs_xvars;_} -> m_urhs_xvars
        | _ -> assert false (* Guarded by the [if ur] *)
      in
      (* Add RHS-only variables to [pr_vars] and get index of the first
         one. *)
      let (pr_vars, pr_xvars_nb) =
        (* If there is no variable introduced in RHS, do nothing (typically
           while scoping regular rewriting rules.) *)
        if Stdlib.(xvars = []) then (pr_vars, 0) else
        let xvars = Array.of_list (List.map snd xvars) in
        (Array.append pr_vars xvars, Array.length xvars)
      in
      (* We put everything together to build the pre-rule. *)
      { pr_sym = sym ; pr_lhs ; pr_vars ; pr_rhs ; pr_arities
      ; pr_names = lhs_names ; pr_xvars_nb }
    else (* Rewrite rule. *)
      { pr_sym = sym ; pr_lhs ; pr_vars ; pr_rhs ; pr_arities
      ; pr_names = lhs_names ; pr_xvars_nb=0 }
  in
  Pos.make r.pos prerule

(** [scope_pattern ss env t] turns a parser-level term [t] into an actual term
    that will correspond to selection pattern (rewrite tactic). *)
let scope_pattern : sig_state -> env -> p_term -> term = fun ss env t ->
  Bindlib.unbox (scope M_Patt ss env t)

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
let scope_rw_patt : sig_state -> env -> p_rw_patt -> (term, tbinder) rw_patt =
  fun ss env s ->
  match s.elt with
  | Rw_Term(t) -> Rw_Term(scope_pattern ss env t)
  | Rw_InTerm(t) -> Rw_InTerm(scope_pattern ss env t)
  | Rw_InIdInTerm(x,t) ->
      let v = new_tvar x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      Rw_InIdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | Rw_IdInTerm(x,t) ->
      let v = new_tvar x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      Rw_IdInTerm(Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | Rw_TermInIdInTerm(u,(x,t)) ->
      let u = scope_pattern ss env u in
      let v = new_tvar x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      Rw_TermInIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
  | Rw_TermAsIdInTerm(u,(x,t)) ->
      let u = scope_pattern ss env u in
      let v = new_tvar x.elt in
      let t = scope_pattern ss ((x.elt,(v, _Kind, None))::env) t in
      Rw_TermAsIdInTerm(u, Bindlib.unbox (Bindlib.bind_var v (lift t)))
