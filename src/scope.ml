(** Scoping. *)

open Console
open Files
open Terms
open Print
open Parser
open Cmd
open Pos

(** Flag to enable a warning if an abstraction is not annotated (with the type
    of its domain). *)
let wrn_no_type : bool ref = ref false

(** Representation of an environment for variables. *)
type env = (string * (tvar * (strloc * tbox))) list

(** Extend an [env] with the mapping [(s,(v,a))] if s <> "_". *)
let add_env : string -> tvar -> (strloc * tbox) -> env -> env =
  fun s v x env -> if s = "_" then env else (s,(v,x))::env

(** [find_var sign env mp x] returns a bindbox corresponding to a variable  of
    the environment [env], or to a symbol named [x] which module path is [mp].
    In the case where [mp] is empty,  we first search [x] in the environement,
    and if it is not mapped we also search in the current signature [sign]. If
    the name does not correspond to anything, the program fails gracefully. *)
let find_var : Sign.t -> env -> qident -> tbox = fun sign env qid ->
  let (mp, x) = qid.elt in
  if mp = [] then
    (* No module path, search the environment first. *)
    begin
      try Bindlib.box_of_var (fst (List.assoc x env)) with Not_found ->
      try _Symb (Sign.find sign x) with Not_found ->
      fatal "Unbound variable or symbol %S...\n%!" x
    end
  else if not Sign.(mp = sign.path || Hashtbl.mem sign.deps mp) then
    (* Module path is not available (not loaded), fail. *)
    begin
      let cur = String.concat "." Sign.(sign.path) in
      let req = String.concat "." mp in
      fatal "No module %s loaded in %s...\n%!" req cur
    end
  else
    (* Module path loaded, look for symbol. *)
    begin
      (* Cannot fail. *)
      let sign = try Hashtbl.find Sign.loaded mp with _ -> assert false in
      try _Symb (Sign.find sign x) with Not_found ->
      fatal "Unbound symbol %S...\n%!" (String.concat "." (mp @ [x]))
    end

(** Given a boxed context [x1:T1, .., xn:Tn] and a boxed term [t] with
    free variables in [x1, .., xn], build the product type [x1:T1 ->
    .. -> xn:Tn -> t]. *)
let build_prod : env -> tbox -> term = fun c t ->
  let fn b (_,(v,(_,a))) =
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

(** [scope new_wildcard env sign t] transforms the parsing level term [t] into
    an actual term using the free variables of the environment [env], and  the
    symbols of the signature [sign]. Wildcards are replaced by new
    metavariables. *)
let scope : (unit -> tbox) option -> env -> Sign.t -> p_term -> tbox =
  fun new_wildcard env sign t ->
    let rec scope env t =
      match t.elt with
      | P_Vari(qid)   -> find_var sign env qid
      | P_Type        -> _Type
      | P_Prod(x,a,b) ->
          let a = scope env a in
          let f v = scope (add_env x.elt v (x,a) env) b in
          _Prod a x.elt f
      | P_Abst(x,ao,b) ->
          let a =
            match ao with
            | Some(a) -> scope env a
            | None    -> build_meta_app env true
          in
          let f v = scope (add_env x.elt v (x,a) env) b in
          _Abst a x.elt f
      | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
      | P_Wild        ->
          begin
            match new_wildcard with
            | Some(f) -> f ()
            | None    -> build_meta_app env false
          end
      | P_Meta(id,ts) ->
        let ts = Array.map (scope env) ts in
        let m =
          match id with
          | M_Bad k -> fatal "Unknown metavariable [?%i] %a" k Pos.print t.pos
          | M_Sys k ->
             begin
              try find_meta (Internal k)
              with Not_found -> assert false
             (* Cannot happen since the existence of [k] is checked
               during parsing. *)
             end
          | M_User s ->
             let id = Defined s in
             begin
              try find_meta id
              with Not_found ->
                let t, _ = build_meta_type env false in
                add_meta s t (List.length env)
             end
        in
        _Meta m ts
    in
    scope env t

(** [to_tbox ~env sign t] is a convenient interface for [scope]. *)
let to_tbox : ?env:env -> Sign.t -> p_term -> tbox =
  fun ?(env=[]) sign t -> scope None env sign t

(** [to_term ~env sign t] composes [to_tbox] with [Bindlib.unbox]. *)
let to_term : ?env:env -> Sign.t -> p_term -> term =
  fun ?(env=[]) sign t -> Bindlib.unbox (scope None env sign t)

(** Representation of a pattern as its head symbol, the list of its arguments,
    and an array of variables corresponding to wildcards. *)
type patt = def * tbox list * tvar array

(** [to_patt env sign t] transforms the parsing level term [t] into a pattern.
    Note that [t] may contain wildcards. The function also checks that it  has
    a definable symbol as a head term, and gracefully fails otherwise. *)
let to_patt : env -> Sign.t -> p_term -> patt = fun env sign t ->
  let wildcards = ref [] in
  let counter = ref 0 in
  let new_wildcard () =
    let x = "#" ^ string_of_int !counter in
    let x = Bindlib.new_var mkfree x in
    incr counter; wildcards := x :: !wildcards; Bindlib.box_of_var x
  in
  let t = Bindlib.unbox (scope (Some new_wildcard) env sign t) in
  let (head, args) = get_args t in
  match head with
  | Symb(Def(s)) -> (s, List.map lift args, Array.of_list !wildcards)
  | Symb(Sym(s)) -> fatal "%s is not a definable symbol...\n" s.sym_name
  | _            -> fatal "%a is not a valid pattern...\n" pp t

(* NOTE wildcards are replaced by fresh variables named with a natural number,
   prefixed with the ['#'] character.  This means that wildcards are syntactic
   sugar for fresh variables with a single occurence (in the pattern). This is
   useful as the corresponding variables may appear in constraints, when rules
   are type-checked. *)

(** [scope_rule sign r] scopes a parsing level reduction rule, producing every
    element that is necessary to check its type and print error messages. This
    includes the context the symbol, the LHS / RHS as terms and the rule. *)
let scope_rule : Sign.t -> p_rule -> ctxt * def * term * term * rule =
  fun sign (xs_ty_map,t,u) ->
    (*Reminder: type p_rule = (strloc * p_term option) list * p_term * p_term*)
    let xs = List.map fst xs_ty_map in
    (* Scoping the LHS and RHS. *)
    let env = List.map (fun x -> (x.elt, (Bindlib.new_var mkfree x.elt, (x, _Type) (*FIXME*) ))) xs in
    let (s, l, wcs) = to_patt env sign t in
    (*Reminder: type patt = def * tbox list * tvar array*)
    let arity = List.length l in
    let l = Bindlib.box_list l in
    let u = to_tbox ~env sign u in
    (* Building the definition. *)
    let xs = Array.of_list (List.map (fun (_,(v,_)) -> v) env) in
    let lhs =
      let lhs = Bindlib.bind_mvar xs l in
      let lhs = Bindlib.bind_mvar wcs lhs in
      let lhs = Bindlib.unbox lhs in
      Bindlib.msubst lhs (Array.map (fun _ -> Wild) wcs)
    in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs u) in
    (* Constructing the typing context. *)
    let xs = Array.append xs wcs in
    let xs_ty_map = List.map (fun (n,a) -> (n.elt,a)) xs_ty_map in
    let ty_map = List.map (fun (n,(x,_)) -> (x, List.assoc n xs_ty_map)) env in
    let fn x =
      let n = Bindlib.name_of x in
      (n, (x, (Pos.none n, _Type)))
    in
    let add_var (env, ctx) x =
      let a =
        try
          match snd (List.find (fun (y,_) -> Bindlib.eq_vars y x) ty_map) with
          | None    -> raise Not_found
          | Some(a) -> to_tbox ~env sign a (* FIXME order ? *)
        with Not_found ->
          (* FIXME order (temporary hack.
          let fn (_,x) = Bindlib.box_of_var x in
          let vars = List.map fn vars in
          Bindlib.unbox (_Meta (new_meta ()) (Array.of_list vars))
          *)
          _Meta (new_meta Type 0) (Array.map Bindlib.box_of_var xs)
      (* We use dummy values for the context and type since they are
         not used in the current type-checking algorithm. *)
      in
      (fn x :: env, add_tvar x (Bindlib.unbox a) ctx)
    in
    let wcs = Array.to_list wcs in
    let wcs = List.map fn wcs in
    let (_, ctx) = Array.fold_left add_var (wcs, empty_ctxt) xs in
    (* Constructing the rule. *)
    let t = add_args (Symb(Def s)) (Bindlib.unbox l) in
    let u = Bindlib.unbox u in
    (ctx, s, t, u, { lhs ; rhs ; arity })

(** [scope_cmd_aux sign cmd] scopes the parser level command [cmd],  using the
    signature [sign]. In case of error, the program gracefully fails. *)
let scope_cmd_aux : Sign.t -> p_cmd -> cmd_aux = fun sign cmd ->
  match cmd with
  | P_NewSym(x,a)       -> NewSym(x, to_term sign a)
  | P_NewDef(x,a)       -> NewDef(x, to_term sign a)
  | P_Def(o,x,a,t)      ->
      let t = to_term sign t in
      let a =
        match a with
        | None    ->
            begin
              match Typing.infer sign empty_ctxt t with
              | Some(a) -> a
              | None    -> fatal "Unable to infer the type of [%a]\n" pp t
            end
        | Some(a) -> to_term sign a
      in
      Def(o, x, a, t)
  | P_Rules(rs)         -> Rules(List.map (scope_rule sign) rs)
  | P_Import(path)      -> Import(path)
  | P_Debug(b,s)        -> Debug(b,s)
  | P_Verb(n)           -> Verb(n)
  | P_Infer(t,c)        -> Infer(to_term sign t, c)
  | P_Eval(t,c)         -> Eval(to_term sign t, c)
  | P_Test_T(ia,mf,t,a) ->
      let contents = HasType(to_term sign t, to_term sign a) in
      Test({is_assert = ia; must_fail = mf; contents})
  | P_Test_C(ia,mf,t,u) ->
      let contents = Convert(to_term sign t, to_term sign u) in
      Test({is_assert = ia; must_fail = mf; contents})
  | P_Other(c)          -> Other(c)

(** [scope_cmd_aux sign cmd] scopes the parser level command [cmd],  using the
    signature [sign], and forwards the source code position of the command. In
    case of error, the program gracefully fails. *)
let scope_cmd : Sign.t -> p_cmd loc -> cmd = fun sign cmd ->
  {elt = scope_cmd_aux sign cmd.elt; pos = cmd.pos}
