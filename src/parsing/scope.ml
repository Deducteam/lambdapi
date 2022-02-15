(** Scoping. Convert parsed terms in core terms by finding out which
   identifiers are bound variables or function symbol declared in open
   modules. *)

open Lplib
open Common open Error open Pos open Debug
open Syntax
open Core open Term open Env open Sig_state open Print

let term = Raw.term

(** Logging function for term scoping. *)
let log_scop = Logger.make 'o' "scop" "term scoping"
let log_scop = log_scop.pp

(** [find_qid prt prv ss env qid] returns a boxed term corresponding to a
   variable of the environment [env] (or to a symbol) which name corresponds
   to [qid]. In the case where the module path [fst qid.elt] is empty, we
   first search for the name [snd qid.elt] in the environment, and if it is
   not mapped we also search in the opened modules. The exception [Fatal] is
   raised if an error occurs (e.g., when the name cannot be found). If [prt]
   is true, protected symbols from external modules are allowed (protected
   symbols from current modules are always allowed). If [prv] is true, private
   symbols are allowed. *)
let find_qid : bool -> bool -> sig_state -> env -> p_qident -> term =
  fun prt prv ss env qid ->
  if Logger.log_enabled () then log_scop "find_qid %a" Pretty.qident qid;
  let (mp, s) = qid.elt in
  (* Check for variables in the environment first. *)
  try
    if mp <> [] then raise Not_found; (* Variables cannot be qualified. *)
    mk_Vari (Env.find s env)
  with Not_found ->
    (* Check for symbols. *)
    mk_Symb (find_sym ~prt ~prv ss qid)

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
      { m_term_meta_of_key : int -> meta option
      (** Allows to retrieve generated metas by their key. *)
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
      ; m_rhs_data : (string, int) Hashtbl.t
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
      ; m_urhs_xvars : (string, int) Hashtbl.t
      (** Variables scoped that  were not in the LHS. This  field is only used
          in  unification  rules and  is  updated  imperatively for  each  new
          variable scoped. A couple [(n, v)]  is the name of the variable with
          the variable itself. The name is needed to ensure that two variables
          with the same name are scoped as the same variable. *)
      ; m_urhs_data : (string, int) Hashtbl.t }
  (** Scoping mode for unification rule right-hand sides. During  scoping, we
      always have [m_urhs_vars_nb = m_lhs_size + length m_urhs_xvars]. *)

(** [scope_iden md ss env qid] scopes [qid] as a symbol. *)
let scope_iden : mode -> sig_state -> env -> p_qident -> term =
  fun md ss env qid ->
  let prt = match md with M_LHS _ -> true | _ -> false
  and prv =
    match md with
    | M_LHS(d) -> d.m_lhs_prv
    | M_Term(d) -> d.m_term_prv
    | M_RHS(d) -> d.m_rhs_prv
    | _ -> false
  in
  find_qid prt prv ss env qid

(** [fresh_patt name ts] creates a unique pattern variable applied to
   [ts]. [name] is used as suffix if distinct from [None]. *)
let fresh_patt : lhs_data -> string option -> term array -> term =
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
      mk_Patt (Some i, name, ts)
  | None ->
      let i = fresh_index () in
      mk_Patt (Some i, string_of_int i, ts)

(** [is_invalid_bindlib_id s] says whether [s] can be safely used as variable
   name in  Indeed, because converts any suffix consisting of
   a sequence of digits into an integer, and increment it, we cannot use as
   bound variable names escaped identifiers or regular identifiers ending with
   a non-negative integer with leading zeros. *)
let is_invalid_bindlib_id : string -> bool =
  let rec last_digit s k =
    let l = k-1 in
    if l < 0 then 0 else
      match s.[l] with
      | '0' .. '9' -> last_digit s l
      | _ -> k
  in
  fun s ->
    let n = String.length s - 1 in
    n >= 0 &&
    match s.[n] with
    | '0' .. '9' -> let k = last_digit s n in s.[k] = '0' && k < n
    | '}' -> true
    | _ -> false

(* unit tests *)
let _ =
  let invalid = is_invalid_bindlib_id in
  let valid s = not (invalid s) in
  assert (invalid "00");
  assert (invalid "01");
  assert (invalid "a01");
  assert (invalid "{|:|}");
  assert (valid "_x_100");
  assert (valid "_z1002");
  assert (valid "case_ex2_intro");
  assert (valid "case_ex02_intro");
  assert (valid "case_ex02_intro0");
  assert (valid "case_ex02_intro1");
  assert (valid "case_ex02_intro10")

let pp_env : env Base.pp =
  let open Base in
  let def ppf t = out ppf " ≔ %a" term t in
  let elt ppf (s, (_,a,t)) = out ppf "%s: %a%a" s term a (Option.pp def) t in
  (D.list elt)

(** [scope ~typ md ss env t] turns a parser-level term [t] into an actual
    term. The variables of the environment [env] may appear in [t],
    and the scoping mode [md] changes the behaviour related to certain
    constructors. The signature state [ss] is used to convert identifiers
    into symbols according to [find_qid]. If [typ] is true, then [t]
    must be a type (defaults to false). *)
let rec scope : ?typ:bool -> int -> mode -> sig_state -> env -> p_term ->
  term =
  fun ?(typ=false) k md ss env t ->
  scope_parsed ~typ k md ss env (Pratt.parse ss env t)

(** [scope_parsed ~typ md ss env t] turns a parser-level, Pratt-parsed
    term [t] into an actual term. *)
and scope_parsed :
  ?typ:bool -> int -> mode -> sig_state -> env -> p_term -> term =
  fun ?(typ=false) k md ss env t ->
  if Logger.log_enabled () then
    log_scop "%a<= %a@ %a" D.depth k pp_env env Pretty.term t;
  (* Extract the spine. *)
  let p_head, args = Syntax.p_get_args t in
  (* Check that LHS pattern variables are applied to no argument. *)
  begin
    match p_head.elt, md with
    | P_Patt _, M_LHS _ when args <> [] ->
      begin match args with
        | [{elt=P_Expl _;_}] ->
          fatal t.pos "Explicit terms are forbidden in rule LHS. \
                       You perhaps forgot to write a dot before?"
        | _ -> fatal t.pos "Pattern variables cannot be applied."
      end
    | _ -> ()
  end;
  (* Scope the head and obtain the implicitness of arguments. *)
  let h = scope_head ~typ k md ss env p_head in
  (* Find out whether [h] has implicit arguments. *)
  let rec get_impl p_head =
    match p_head.elt with
    | P_Wrap e -> get_impl e
    | P_Iden (_, false) ->
        (* We avoid unboxing if [h] is not closed (and hence not a symbol). *)
        if is_closed h then
          match h with
          | Symb s -> s.sym_impl
          | _ -> []
        else []
    | P_Abst (params_list, t) ->
      Syntax.get_impl_params_list params_list @ get_impl t
    | _ -> []
  in
  let impl =
    match p_head.elt, args with
    | P_Abst _, [] -> []
    | _ -> minimize_impl (get_impl p_head)
  in
  (* Scope and insert the (implicit) arguments. *)
  add_impl k md ss env t.pos h impl args
  |> D.log_and_return (fun e -> log_scop "%a=> %a" D.depth k term e)

(** [add_impl md ss env loc h impl args] scopes [args] and returns the
   application of [h] to the scoped arguments. [impl] is a boolean list
   described the implicit arguments. Implicit arguments are added as
   underscores before scoping. *)
and add_impl : int -> mode -> sig_state ->
               Env.t -> popt -> term -> bool list -> p_term list -> term =
  fun k md ss env loc h impl args ->
  let appl = match md with M_LHS _ -> mk_Appl_not_canonical | _ -> mk_Appl in
  let appl_p_term t u = appl (t, scope_parsed (k+1) md ss env u) in
  let appl_meta t = appl (t, scope_head (k+1) md ss env P.wild) in
  match impl, args with
  (* The remaining arguments are all explicit. *)
  | [], _ -> List.fold_left appl_p_term h args
  (* Only implicit arguments remain. *)
  | true::impl, [] -> add_impl k md ss env loc (appl_meta h) impl []
  (* The first argument is implicit (could be [a] if made explicit). *)
  | true::impl, a::args ->
      begin match a.elt with
      | P_Expl b ->
          add_impl k md ss env loc
            (appl_p_term h {a with elt = P_Wrap b}) impl args
      | _ -> add_impl k md ss env loc (appl_meta h) impl (a::args)
      end
  (* The first argument [a] is explicit. *)
  | false::impl, a::args ->
      begin match a.elt with
      | P_Expl _ -> fatal a.pos "Unexpected explicit argument."
      | _ -> add_impl k md ss env loc (appl_p_term h a) impl args
      end
  (* The application is too "partial" to insert all implicit arguments. *)
  | false::_, [] ->
      (* NOTE this could be improved with more general implicits. *)
      fatal loc "More arguments are required to instantiate implicits."

(** [scope_domain md ss env t] scopes [t] as the domain of an abstraction or
   product. *)
and scope_domain : int -> mode -> sig_state -> env -> p_term option -> term =
  fun k md ss env a ->
  match a, md with
  | (Some {elt=P_Wild;_}|None), M_LHS data ->
      fresh_patt data None (Env.to_terms env)
  | (Some {elt=P_Wild;_}|None), _ -> mk_Plac true
  | Some a, _ -> scope ~typ:true k md ss env a

(** [scope_binder ~typ mode ss cons env params_list t] scopes [t] in
   mode [md], signature state [ss] and environment [env]. [params_list] is a
   list of paramters to abstract on. For each parameter, a tbox is built using
   [cons] (either [_Abst] or [_Prod]). If [warn] is true (the default), a
   warning is printed when the variable that is bound by the binder does not
   appear in the body. [typ] indicates if we scope a type (default is
   false). *)
and scope_binder : ?typ:bool -> int -> mode -> sig_state ->
  (term * binder -> term) -> Env.t -> p_params list ->
  p_term option -> term =
  fun ?(typ=false) k md ss cons env params_list t ->
  let rec scope_params_list env params_list =
    match params_list with
    | [] ->
        begin
          match t with
          | Some t -> scope ~typ (k+1) md ss env t
          | None -> mk_Plac true
        end
    | (idopts,typopt,_implicit)::params_list ->
      let dom = scope_domain (k+1) md ss env typopt in
      scope_params env idopts dom params_list
  and scope_params env idopts a params_list =
    let rec aux env idopts =
      match idopts with
      | [] -> scope_params_list env params_list
      | None::idopts ->
          let v = new_var "_" in
          let t = aux env idopts in
          cons (a, bind_var v t)
      | Some {elt=id;pos}::idopts ->
          if is_invalid_bindlib_id id then
            fatal pos "\"%s\": Escaped identifiers or regular identifiers \
                       having an integer suffix with leading zeros \
                       are not allowed for bound variable names." id;
          let v = new_var id in
          let env = Env.add id v a None env in
          let t = aux env idopts in
          cons (a, bind_var v t)
    in aux env idopts
  in
  scope_params_list env params_list

(** [scope_head ~typ md ss env t] scopes [t] as term head. *)
and scope_head :
  ?typ:bool -> int -> mode -> sig_state -> env -> p_term -> term =
  fun ?(typ=false) k md ss env t ->
  match (t.elt, md) with
  | (P_Type, M_LHS(_)) -> fatal t.pos "TYPE is not allowed in a LHS."
  | (P_Type, _) -> mk_Type

  | (P_Iden(qid,_), _) -> scope_iden md ss env qid

  | (P_NLit(0), _) ->
    begin match Builtin.get_opt ss "0" with
      | Some s -> mk_Symb s
      | None -> scope_iden md ss env {t with elt=([],"0")}
    end
  | (P_NLit(n), _) ->
    begin match Builtin.get_opt ss "0" with
      | None -> scope_iden md ss env {t with elt=([], string_of_int n)}
      | Some sym_z ->
        match Builtin.get_opt ss "+1" with
        | Some sym_s ->
          let z = mk_Symb sym_z and s = mk_Symb sym_s in
          let rec unsugar_nat_lit acc n =
            if n <= 0 then acc else unsugar_nat_lit (mk_Appl(s,acc)) (n-1) in
          unsugar_nat_lit z n
        | None -> scope_iden md ss env {t with elt=([], string_of_int n)}
    end

  | (P_Wild, M_URHS(data)) ->
    let i = data.m_urhs_vars_nb in
    data.m_urhs_vars_nb <- data.m_urhs_vars_nb + 1;
    mk_Patt (Some i, "_", Env.to_terms env)
  | (P_Wild, M_LHS data) -> fresh_patt data None (Env.to_terms env)
  | (P_Wild, M_Patt) -> mk_Wild
  | (P_Wild, (M_RHS _|M_Term _)) -> mk_Plac typ

  | (P_Meta({elt;pos} as mk,ts), M_Term {m_term_meta_of_key;_}) -> (
      match m_term_meta_of_key elt with
      | None ->
          fatal pos "Metavariable %a not found among generated variables: \
                     metavariables can only be created by the system."
            Pretty.meta_ident mk
      | Some m -> mk_Meta (m, Array.map (scope (k + 1) md ss env) ts))
  | (P_Meta(_), _) -> fatal t.pos "Metavariables are not allowed here."

  | (P_Patt(id,ts), M_LHS(d)) ->
      (* Check that [ts] are variables. *)
      let scope_var t =
        match unfold (scope (k+1) md ss env t) with
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
                if eq_vars vs.(i) vs.(j) then
                  fatal ts.(j).pos
                    "Variable %a appears more than once \
                     in the environment of a pattern variable."
                    var vs.(j)
              done
            done;
            Array.map mk_Vari vs
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
      let i =
        match id with
        | None     -> fatal t.pos "Wildcard pattern not allowed in a URHS."
        | Some {elt=id;_} ->
            (* Search in variables declared in LHS. *)
            try Hashtbl.find r.m_urhs_data id
            with Not_found ->
              (* Search in variables already declared in RHS. *)
              try Hashtbl.find r.m_urhs_xvars id
              with Not_found ->
                let i = r.m_urhs_vars_nb in
                Hashtbl.add r.m_urhs_xvars id i;
                r.m_urhs_vars_nb <- r.m_urhs_vars_nb + 1;
                i
      in
      let ts =
        match ts with
        | None -> [||] (* $M stands for $M[] *)
        | Some ts -> Array.map (scope (k+1) md ss env) ts
      in
      let name = match id with Some {elt;_} -> elt | None -> assert false in
      mk_Patt (Some i, name, ts)
  | (P_Patt(id,ts), M_RHS(r)) ->
      let i =
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
        | Some ts -> Array.map (scope (k+1) md ss env) ts
      in
      let name = match id with Some {elt;_} -> elt | None -> assert false in
      mk_Patt (Some i, name, ts)
  | (P_Patt(_,_), _) ->
      fatal t.pos "Pattern variables are only allowed in rewriting rules."

  | (P_Appl(_,_), _) ->  assert false (* Unreachable. *)

  | (P_Arro(_,_), M_Patt) ->
      fatal t.pos "Arrows are not allowed in patterns."
  | (P_Arro(a,b), _) ->
    mk_Arro (scope ~typ:true (k+1) md ss env a,
             scope ~typ:true (k+1) md ss env b)

  | (P_Abst(_,_), M_Patt) ->
      fatal t.pos "Abstractions are not allowed in patterns."
  | (P_Abst(xs,t), _) -> scope_binder k md ss mk_Abst env xs (Some(t))

  | (P_Prod(_,_), M_Patt) ->
      fatal t.pos "Dependent products are not allowed in patterns."
  | (P_Prod(xs,b), _) ->
    scope_binder ~typ:true k md ss mk_Prod env xs (Some(b))

  | (P_LLet(x,xs,a,t,u), (M_Term _|M_URHS _|M_RHS _)) ->
      let a = scope_binder ~typ:true (k+1) md ss mk_Prod env xs a in
      let t = scope_binder (k+1) md ss mk_Abst env xs (Some(t)) in
      let v = new_var x.elt in
      let u = scope ~typ (k+1) md ss (Env.add x.elt v a (Some(t)) env) u in
      if not (occur v u) then
        wrn x.pos "Useless let-binding (%s is not bound)." x.elt;
      mk_LLet (a, t, bind_var v u)
  | (P_LLet(_), M_LHS(_)) ->
      fatal t.pos "Let-bindings are not allowed in a LHS."
  | (P_LLet(_), M_Patt) ->
      fatal t.pos "Let-bindings are not allowed in patterns."

  (* Evade the addition of implicit arguments inside the wrap *)
  | (P_Wrap ({ elt = (P_Iden _ | P_Abst _); _ } as id), _) ->
    scope_head ~typ k md ss env id
  | (P_Wrap t, _) -> scope ~typ k md ss env t

  | (P_Expl(_), _) -> fatal t.pos "Explicit argument not allowed here."

let scope =
  let open Stdlib in let r = ref mk_Kind in fun ?(typ=false) k md ss env t ->
  Debug.(record_time Scoping (fun () -> r := scope ~typ k md ss env t)); !r

(** [scope ~typ ~mok prv expo ss env p t] turns a pterm [t] into a term in
    the signature state [ss] and environment [env] (for bound
    variables). If [expo] is {!constructor:Public}, then the term must not
    contain any private subterms. If [~typ] is [true], then [t] must be
    a type (defaults to [false]). No {b new} metavariables may appear in
    [t], but metavariables in the image of [mok] may be used. The function
    [mok] defaults to the function constant to [None] *)
let scope_term : ?typ:bool -> ?mok:(int -> meta option) ->
  bool -> sig_state -> env -> p_term -> term =
  fun ?(typ=false) ?(mok=fun _ -> None) m_term_prv ss env t ->
  let md = M_Term {m_term_meta_of_key=mok; m_term_prv} in
  scope ~typ 0 md ss env t

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

(** [scope_rule ur ss r] turns a parser-level rewriting rule [r], or a
    unification rule if [ur] is true, into a pre-rewriting rule. *)
let scope_rule : bool -> sig_state -> p_rule -> sym_rule =
  fun ur ss { elt = (p_lhs, p_rhs); pos = rule_pos } ->
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
  let (lhs, lhs_indices, lhs_arities, vars_nb) =
    let mode =
      M_LHS{ m_lhs_prv     = is_private (get_root ss [] p_lhs)
           ; m_lhs_indices = Hashtbl.create 7
           ; m_lhs_arities = Hashtbl.create 7
           ; m_lhs_names   = Hashtbl.create 7
           ; m_lhs_size    = 0
           ; m_lhs_in_env  = nl @ List.map fst pvs_rhs }
    in
    let lhs = scope 0 mode ss Env.empty p_lhs in
    match mode with
    | M_LHS{ m_lhs_indices; m_lhs_size; m_lhs_arities; m_lhs_names;
             m_lhs_in_env; _ } -> let open D in
      if Logger.log_enabled() then
        log_scop "@[<v>lhs_size %d@ lhs_indices %a@ lhs_arities %a\
                  @ lhs_names %a@ lhs_in_env %a@]" m_lhs_size
          (hashtbl string int) m_lhs_indices
          (hashtbl int int) m_lhs_arities
          (hashtbl int string) m_lhs_names
          (list string) m_lhs_in_env;
      (lhs, m_lhs_indices, m_lhs_arities, m_lhs_size)
    | _ -> assert false
  in
  (* Check the head symbol and build the actual LHS. *)
  let (sym, lhs) =
    let (h, args) = get_args lhs in
    match h with
    | Symb(s) ->
        if is_constant s then fatal p_lhs.pos "Constant LHS head symbol.";
        if s.sym_expo = Protec && ss.signature.sign_path <> s.sym_path then
          fatal p_lhs.pos "Cannot define rules on foreign protected symbols.";
        (s, args)
    | _ -> fatal p_lhs.pos "No head symbol in LHS."
  in
  if Timed.(!(sym.sym_def)) <> None then
    fatal rule_pos "No rewriting rule can be given on a defined symbol.";
  (* Create the pattern variables that can be bound in the RHS. *)
  let mode =
    if ur then
      M_URHS{ m_urhs_data = lhs_indices
            ; m_urhs_vars_nb = vars_nb
            ; m_urhs_xvars = Hashtbl.create 7 }
    else
      M_RHS{ m_rhs_prv = is_private sym
           ; m_rhs_data = lhs_indices
           ; m_rhs_new_metas = new_problem() }
  in
  let rhs = scope 0 mode ss Env.empty p_rhs in
  let arities =
    let f i = try Hashtbl.find lhs_arities i with Not_found -> assert false in
    Array.init vars_nb f
  in
  let xvars_nb =
    match mode with
    | M_URHS{m_urhs_vars_nb; _} -> m_urhs_vars_nb - vars_nb
    | _ -> 0
  in
  let arity = List.length lhs in
  let r = {lhs; rhs; arity; arities; vars_nb; xvars_nb; rule_pos} in
  (sym,r)

(** [scope_pattern ss env t] turns a parser-level term [t] into an actual term
    that will correspond to selection pattern (rewrite tactic). *)
let scope_pattern : sig_state -> env -> p_term -> term = fun ss env t ->
  scope 0 M_Patt ss env t

(** [scope_rw_patt ss env t] turns a parser-level rewrite tactic specification
    [s] into an actual rewrite specification (possibly containing variables of
    [env] and using [ss] for aliasing). *)
let scope_rw_patt : sig_state -> env -> p_rw_patt -> (term, binder) rw_patt =
  fun ss env s ->
  match s.elt with
  | Rw_Term(t) -> Rw_Term(scope_pattern ss env t)
  | Rw_InTerm(t) -> Rw_InTerm(scope_pattern ss env t)
  | Rw_InIdInTerm(x,t) ->
      let v = new_var x.elt in
      let t = scope_pattern ss ((x.elt,(v, mk_Kind, None))::env) t in
      Rw_InIdInTerm(bind_var v t)
  | Rw_IdInTerm(x,t) ->
      let v = new_var x.elt in
      let t = scope_pattern ss ((x.elt,(v, mk_Kind, None))::env) t in
      Rw_IdInTerm(bind_var v t)
  | Rw_TermInIdInTerm(u,(x,t)) ->
      let u = scope_pattern ss env u in
      let v = new_var x.elt in
      let t = scope_pattern ss ((x.elt,(v, mk_Kind, None))::env) t in
      Rw_TermInIdInTerm(u, bind_var v t)
  | Rw_TermAsIdInTerm(u,(x,t)) ->
      let u = scope_pattern ss env u in
      let v = new_var x.elt in
      let t = scope_pattern ss ((x.elt,(v, mk_Kind, None))::env) t in
      Rw_TermAsIdInTerm(u, bind_var v t)
