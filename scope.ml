(** Scoping. *)

open Console
open Files
open Terms
open Print
open Parser

(** Representation of an environment for variables. *)
type env = (string * tvar) list

(** [scope new_wildcard env sign t] transforms the parsing level term [t] into
    an actual term using the free variables of the environement [env], and the
    symbols of the signature [sign]. If a function is given in [new_wildcard],
    then it is called on [P_Wild] nodes. This is only allowed when considering
    [t] as a pattern. *)
let scope : (unit -> tbox) option -> env -> Sign.t -> p_term -> tbox =
  fun new_wildcard vars sign t ->
    let rec scope vars t =
      match t with
      | P_Vari([],x)  ->
          begin
            try Bindlib.box_of_var (List.assoc x vars) with Not_found ->
            try _Symb (Sign.find sign x) with Not_found ->
            fatal "Unbound variable or symbol %S...\n%!" x
          end
      | P_Vari(fs,x)  ->
          begin
            if not (fs = Sign.(sign.path) || Hashtbl.mem Sign.(sign.deps) fs) then
              begin
                let cur = String.concat "." Sign.(sign.path) in
                let req = String.concat "." fs in
                fatal "No module %s loaded in %s...\n%!" req cur
              end;
            try
              let sg = Hashtbl.find Sign.loaded fs in
              try _Symb (Sign.find sg x) with Not_found ->
                let x = String.concat "." (fs @ [x]) in
                fatal "Unbound symbol %S...\n%!" x
            with Not_found ->
              let path = String.concat "." fs in
              fatal "No module path %S loaded...\n%!" path
          end
      | P_Type        -> _Type
      | P_Prod(x,a,b) ->
          let f v = scope (if x = "_" then vars else (x,v)::vars) b in
          _Prod (scope vars a) x f
      | P_Abst(x,a,t) ->
          let f v = scope ((x,v)::vars) t in
          let a =
            match a with
            | None    -> let fn (_,x) = Bindlib.box_of_var x in
                         let vars = List.map fn vars in
                         _Unif (new_unif ()) (Array.of_list vars)
            | Some(a) -> scope vars a
          in
          _Abst a x f
      | P_Appl(t,u)   -> _Appl (scope vars t) (scope vars u)
      | P_Wild        ->
          match new_wildcard with
          | None    -> fatal "\"_\" not allowed in terms...\n"
          | Some(f) -> f ()
    in
    scope vars t

(** [to_tbox ~vars sign t] is a convenient interface for [scope]. *)
let to_tbox : ?vars:env -> Sign.t -> p_term -> tbox =
  fun ?(vars=[]) sign t -> scope None vars sign t

(** [to_term ~vars sign t] composes [to_tbox] with [Bindlib.unbox]. *)
let to_term : ?vars:env -> Sign.t -> p_term -> term =
  fun ?(vars=[]) sign t -> Bindlib.unbox (scope None vars sign t)

(** Representation of a pattern as its head symbol, the list of its arguments,
    and an array of variables corresponding to wildcards. *)
type patt = def * tbox list * tvar array

(** [to_patt env sign t] transforms the parsing level term [t] into a pattern.
    Note that [t] may contain wildcards. The function also checks that it  has
    a definable symbol as a head term, and gracefully fails otherwise. *)
let to_patt : env -> Sign.t -> p_term -> patt = fun vars sign t ->
  let wildcards = ref [] in
  let counter = ref 0 in
  let new_wildcard () =
    let x = "#" ^ string_of_int !counter in
    let x = Bindlib.new_var mkfree x in
    incr counter; wildcards := x :: !wildcards; Bindlib.box_of_var x
  in
  let t = Bindlib.unbox (scope (Some new_wildcard) vars sign t) in
  let (head, args) = get_args t in
  match head with
  | Symb(Def(s)) -> (s, List.map lift args, Array.of_list !wildcards)
  | Symb(Sym(s)) -> fatal "%s is not a definable symbol...\n" s.sym_name
  | _            -> fatal "%a is not a valid pattern...\n" pp t

(** [scope_rule sign r] scopes a parsing level reduction rule, producing every
    element that is necessary to check its type and print error messages. This
    includes the context the symbol, the LHS / RHS as terms and the rule. *)
let scope_rule : Sign.t -> p_rule -> Ctxt.t * def * term * term * rule =
  fun sign (xs_ty_map,t,u) ->
    let xs = List.map fst xs_ty_map in
    (* Scoping the LHS and RHS. *)
    let vars = List.map (fun x -> (x, Bindlib.new_var mkfree x)) xs in
    let (s, l, wcs) = to_patt vars sign t in
    let arity = List.length l in
    let l = Bindlib.box_list l in
    let u = to_tbox ~vars sign u in
    (* Building the definition. *)
    let xs = Array.of_list (List.map snd vars) in
    let lhs =
      let lhs = Bindlib.bind_mvar xs l in
      let lhs = Bindlib.bind_mvar wcs lhs in
      let lhs = Bindlib.unbox lhs in
      Bindlib.msubst lhs (Array.map (fun _ -> Wild) wcs)
    in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs u) in
    (* Constructing the typing context. *)
    let xs = Array.append xs wcs in
    let ty_map = List.map (fun (n,x) -> (x, List.assoc n xs_ty_map)) vars in
    let add_var (vars, ctx) x =
      let a =
        try
          match snd (List.find (fun (y,_) -> Bindlib.eq_vars y x) ty_map) with
          | None    -> raise Not_found
          | Some(a) -> to_term ~vars sign a (* FIXME order ? *)
        with Not_found ->
          (* FIXME order (temporary hack.
          let fn (_,x) = Bindlib.box_of_var x in
          let vars = List.map fn vars in
          Bindlib.unbox (_Unif (new_unif ()) (Array.of_list vars))
          *)
          Bindlib.unbox (_Unif (new_unif ()) (Array.map Bindlib.box_of_var xs))
      in
      ((Bindlib.name_of x, x) :: vars, Ctxt.add x a ctx)
    in
    let wcs = Array.to_list wcs in
    let wcs = List.map (fun x -> (Bindlib.name_of x, x)) wcs in
    let (_, ctx) = Array.fold_left add_var (wcs, Ctxt.empty) xs in
    (* Constructing the rule. *)
    let t = add_args (Symb(Def s)) (Bindlib.unbox l) in
    let u = Bindlib.unbox u in
    (ctx, s, t, u, { lhs ; rhs ; arity })

(** Representation of a toplevel command. *)
type cmd =
  (** Static symbol declaration. *)
  | NewSym of string * term
  (** Definable symbol declaration. *)
  | NewDef of string * term
  (** Rewriting rules declaration. *)
  | Rules  of (Ctxt.t * def * term * term * rule) list
  (** Quick definition. *)
  | Defin  of string * term * term
  (** Import an external signature. *)
  | Import of module_path
  (** Set debugging flags. *)
  | Debug  of bool * string
  (** Set the verbosity level. *)
  | Verb   of int
  (** Type-checking command. *)
  | Check  of term * term
  (** Type inference command. *)
  | Infer  of term
  (** Normalisation command. *)
  | Eval   of term
  (** Convertibility command. *)
  | Conv   of term * term
  (** Unimplemented command. *)
  | Other  of string

(** [scope_cmd sign cmd] scopes the parser level command [cmd],  using [sign].
    In case of error, the program gracefully fails. *)
let scope_cmd : Sign.t -> p_cmd -> cmd = fun sign cmd ->
  match cmd with
  | P_NewSym(x,a)  -> NewSym(x, to_term sign a)
  | P_NewDef(x,a)  -> NewDef(x, to_term sign a)
  | P_Defin(x,a,t) ->
      begin
        let t = to_term sign t in
        let a =
          match a with
          | None    ->
              begin
                match Typing.infer sign Ctxt.empty t with
                | Some(a) -> a
                | None    -> fatal "Unable to infer the type of [%a]\n" pp t
              end
          | Some(a) -> to_term sign a
        in
        Defin(x, a, t)
      end
  | P_Rules(rs)    -> Rules(List.map (scope_rule sign) rs)
  | P_Import(path) -> Import(path)
  | P_Debug(b,s)   -> Debug(b,s)
  | P_Verb(n)      -> Verb(n)
  | P_Check(t,a)   -> Check(to_term sign t, to_term sign a)
  | P_Infer(t)     -> Infer(to_term sign t)
  | P_Eval(t)      -> Eval(to_term sign t)
  | P_Conv(t,u)    -> Conv(to_term sign t, to_term sign u)
  | P_Other(c)     -> Other(c)
