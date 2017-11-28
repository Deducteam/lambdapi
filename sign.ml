(** Signature for symbols. *)

open Console
open Files
open Terms

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { symbols : (string, symbol) Hashtbl.t
  ; path    : module_path
  ; deps    : (module_path, (string * rule) list) Hashtbl.t }

(* NOTE the [deps] field contains a hashtable binding the [module_path] of the
   required modules, on which the current signature depends, to an association
   list mapping definable symbols (given in these modules) to additional rules
   (defined in the current signature, for symbols defined elsewhere. *)

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> symbol =
  fun sign name -> Hashtbl.find sign.symbols name

(** [loading] contains the [module_path] of the signatures (or files) that are
    being processed. They are stored in a stack due to dependencies. Note that
    the topmost element corresponds to the current module.  If a [module_path]
    appears twice in the stack, then there is a circular dependency. *)
let loading : module_path Stack.t = Stack.create ()

(** [loaded] stores the signatures of the known (already compiled) modules. An
    important invariant is that all the occurences of a single symbol sould be
    physically equal (across different signatures). This requires copying when
    loading an object file. *)
let loaded : (module_path, t) Hashtbl.t = Hashtbl.create 7

(** [create path] creates an empty signature with module path [path]. *)
let create : module_path -> t = fun path ->
  { path ; symbols = Hashtbl.create 37 ; deps = Hashtbl.create 11 }

(** [link sign] establishes physical links between equal symbols. *)
let link : t -> unit = fun sign ->
  let rec link_term t =
    let link_binder b =
      let (x,t) = Bindlib.unbind mkfree b in
      Bindlib.unbox (Bindlib.bind_var x (lift (link_term t)))
    in
    match unfold t with
    | Vari(x)     -> t
    | Type        -> t
    | Kind        -> t
    | Symb(s)     -> Symb(link_symb s)
    | Prod(i,a,b) -> Prod(i, link_term a, link_binder b)
    | Abst(i,a,t) -> Abst(i, link_term a, link_binder t)
    | Appl(i,t,u) -> Appl(i, link_term t, link_term u)
    | Unif(_,_)   -> assert false
    | ITag(_)     -> assert false
  and link_rule r =
    let (xs, lhs) = Bindlib.unmbind mkfree r.lhs in
    let lhs = List.map link_term lhs in
    let lhs = Bindlib.box_list (List.map lift lhs) in
    let lhs = Bindlib.unbox (Bindlib.bind_mvar xs lhs) in
    let (xs, rhs) = Bindlib.unmbind mkfree r.rhs in
    let rhs = lift (link_term rhs) in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs rhs) in
    {r with lhs ; rhs}
  and link_symb s =
    let (name, path) =
      match s with
      | Sym(s) -> (s.sym_name, s.sym_path)
      | Def(s) -> (s.def_name, s.def_path)
    in
    if path = sign.path then s else
    try
      let sign = Hashtbl.find loaded path in
      try find sign name with Not_found -> assert false
    with Not_found -> assert false
  in
  let fn _ sym =
    match sym with
    | Sym(s) -> s.sym_type <- link_term s.sym_type
    | Def(s) -> s.def_type <- link_term s.def_type;
                s.def_rules <- List.map link_rule s.def_rules
  in
  Hashtbl.iter fn sign.symbols;
  let gn path ls =
    let sign = try Hashtbl.find loaded path with Not_found -> assert false in
    let h (n, r) =
      let r = link_rule r in
      let _ =
        match find sign n with
        | Sym(s) -> assert false
        | Def(s) -> s.def_rules <- s.def_rules @ [r]
      in
      (n, r)
    in
    Some(List.map h ls)
  in
  Hashtbl.filter_map_inplace gn sign.deps

(** [new_static sign name a] creates a new, static symbol named [name] of type
    [a] the signature [sign]. The created symbol is also returned. *)
let new_static : t -> string -> term -> sym =
  fun sign sym_name sym_type ->
    if Hashtbl.mem sign.symbols sym_name then
      wrn "Redefinition of symbol %S.\n" sym_name;
    let sym_path = sign.path in
    let sym = { sym_name ; sym_type ; sym_path } in
    Hashtbl.add sign.symbols sym_name (Sym(sym));
    out 2 "(stat) %s\n" sym_name; sym

(** [new_definable sign name a] creates a fresh definable symbol named [name],
    without any reduction rules, and of type [a] in the signature [sign]. Note
    that the created symbol is also returned. *)
let new_definable : t -> string -> term -> def =
  fun sign def_name def_type ->
    if Hashtbl.mem sign.symbols def_name then
      wrn "Redefinition of symbol %S.\n" def_name;
    let def_path = sign.path in
    let def = { def_name ; def_type ; def_rules = [] ; def_path } in
    Hashtbl.add sign.symbols def_name (Def(def));
    out 2 "(defi) %s\n" def_name; def

(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit =
  fun sign fname ->
    let oc = open_out fname in
    Marshal.to_channel oc sign [Marshal.Closures];
    close_out oc

(** [read fname] reads a signature from the file [fname]. *)
let read : string -> t =
  fun fname ->
    let ic = open_in fname in
    let sign = Marshal.from_channel ic in
    close_in ic; sign

(** [add_rule def r] adds the new rule [r] to the definable symbol [def]. When
    the rule does not correspond to a symbol of the current signature,  it  is
    also stored in the dependencies. *)
let add_rule : t -> def -> rule -> unit = fun sign def r ->
  def.def_rules <- def.def_rules @ [r];
  out 2 "(rule) added a rule for symbol %s\n" def.def_name;
  if def.def_path <> sign.path then
    let m =
      try Hashtbl.find sign.deps def.def_path
      with Not_found -> assert false
    in
    Hashtbl.replace sign.deps def.def_path ((def.def_name, r) :: m)
