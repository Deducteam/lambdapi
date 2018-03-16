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
type env = (string * tvar) list

(** [find_var sign env mp x] returns a bindbox corresponding to a variable of
    the environment [env], or to a symbol named [x] with module path [mp]. In
    the case where [mp] is empty, we first search [x] in the environement, and
    if it is not mapped we also search in the current signature [sign]. If the
    name does not correspond to anything, the program fails gracefully. *)
let find_var : Sign.t -> env -> module_path -> string -> tbox =
  fun sign env mp x ->
    if mp = [] then
      (* No module path, search the environment first. *)
      begin
        try Bindlib.box_of_var (List.assoc x env) with Not_found ->
        try _Symb (Sign.find sign x) with Not_found ->
        fatal "Unbound variable or symbol %S...\n%!" x
      end
    else if not Sign.(mp = sign.path || Hashtbl.mem sign.deps mp) then
      (* Module path is not available (not loaded). *)
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

(** [scope new_wildcard env sign t] transforms the parsing level term [t] into
    an actual term using the free variables of the environement [env], and the
    symbols of the signature [sign]. If a function is given in [new_wildcard],
    then it is called on [P_Wild] nodes. This is only allowed when considering
    [t] as a pattern. *)
let scope : (unit -> tbox) option -> env -> Sign.t -> p_term -> tbox =
  fun new_wildcard env sign t ->
    let rec scope env t =
      match t.elt with
      | P_Vari(mp,x)  -> find_var sign env mp x
      | P_Type        -> _Type
      | P_Prod(x,a,b) ->
          let f v = scope (if x.elt = "_" then env else (x.elt,v)::env) b in
          _Prod (scope env a) x.elt f
      | P_Abst(x,a,t) ->
          let f v = scope ((x.elt,v)::env) t in
          let a =
            match a with
            | None    ->
                if !wrn_no_type then
                  wrn "No type provided for %s at %a\n" x.elt Pos.print x.pos;
                let fn (_,x) = Bindlib.box_of_var x in
                let vars = List.map fn env in
                _Meta (new_meta Ctxt.empty Type) (Array.of_list vars)
	    (* We use dummy values for the context and type since they
	       are not used in the current type-checking algorithm. *)
            | Some(a) ->
                scope env a
          in
          _Abst a x.elt f
      | P_Appl(t,u)   -> _Appl (scope env t) (scope env u)
      | P_Wild        ->
          begin match new_wildcard with
          | None    -> fatal "\"_\" not allowed in terms...\n"
          | Some(f) -> f ()
	  end
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
    let xs = List.map fst xs_ty_map in
    (* Scoping the LHS and RHS. *)
    let env = List.map (fun x -> (x.elt, Bindlib.new_var mkfree x.elt)) xs in
    let (s, l, wcs) = to_patt env sign t in
    let arity = List.length l in
    let l = Bindlib.box_list l in
    let u = to_tbox ~env sign u in
    (* Building the definition. *)
    let xs = Array.of_list (List.map snd env) in
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
    let ty_map = List.map (fun (n,x) -> (x, List.assoc n xs_ty_map)) env in
    let add_var (env, ctx) x =
      let a =
        try
          match snd (List.find (fun (y,_) -> Bindlib.eq_vars y x) ty_map) with
          | None    -> raise Not_found
          | Some(a) -> to_term ~env sign a (* FIXME order ? *)
        with Not_found ->
          (* FIXME order (temporary hack.
          let fn (_,x) = Bindlib.box_of_var x in
          let vars = List.map fn vars in
          Bindlib.unbox (_Meta (new_meta ()) (Array.of_list vars))
          *)
          Bindlib.unbox
	    (_Meta (new_meta Ctxt.empty Type) (Array.map Bindlib.box_of_var xs))
      (* We use dummy values for the context and type since they are
	 not used in the current type-checking algorithm. *)
      in
      ((Bindlib.name_of x, x) :: env, add_tvar x a ctx)
    in
    let wcs = Array.to_list wcs in
    let wcs = List.map (fun x -> (Bindlib.name_of x, x)) wcs in
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
      begin
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
      end
  | P_Rules(rs)         -> Rules(List.map (scope_rule sign) rs)
  | P_Import(path)      -> Import(path)
  | P_Debug(b,s)        -> Debug(b,s)
  | P_Verb(n)           -> Verb(n)
  | P_Infer(t,c)        -> Infer(to_term sign t, c)
  | P_Eval(t,c)         -> Eval(to_term sign t, c)
  | P_Test_T(ia,mf,t,a) ->
      let t = to_term sign t in
      let a = to_term sign a in
      Test({is_assert = ia; must_fail = mf; contents = HasType(t,a)})
  | P_Test_C(ia,mf,t,u) ->
      let t = to_term sign t in
      let u = to_term sign u in
      Test({is_assert = ia; must_fail = mf; contents = Convert(t,u)})
  | P_Other(c)          -> Other(c)

(** [scope_cmd_aux sign cmd] scopes the parser level command [cmd],  using the
    signature [sign], and forwards the source code position of the command. In
    case of error, the program gracefully fails. *)
let scope_cmd : Sign.t -> p_cmd loc -> cmd = fun sign cmd ->
  {elt = scope_cmd_aux sign cmd.elt; pos = cmd.pos}
