(** Signature for symbols. *)

open Extra
open Timed
open Console
open Files
open Terms
open Syntax
open Pos

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : (sym * Pos.popt) StrMap.t ref
  ; sign_path     : Path.t
  ; sign_deps     : (string * rule) list PathMap.t ref
  ; sign_builtins : sym StrMap.t ref
  ; sign_unops    : (sym * unop ) StrMap.t ref
  ; sign_binops   : (sym * binop) StrMap.t ref
  ; sign_idents   : StrSet.t ref
  ; sign_quants   : SymSet.t ref }

(** NOTE the [deps] field contains a hashtable binding the [module_path] of
    the external modules on which the current signature depends to an
    association list. This association list then maps definable symbols of
    the external module to additional reduction rules defined in the current
    signature. *)

(** [dummy ()] The empty signature. It's a thunk to force the creation of
    a new record on each call (and avoid unwanted sharing). *)
let dummy : unit -> t = fun () ->
  { sign_symbols = ref StrMap.empty; sign_path = []
  ; sign_deps = ref PathMap.empty; sign_builtins = ref StrMap.empty
  ; sign_unops = ref StrMap.empty; sign_binops = ref StrMap.empty
  ; sign_idents = ref StrSet.empty; sign_quants = ref SymSet.empty }

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> sym =
  fun sign name -> fst (StrMap.find name !(sign.sign_symbols))

(** [mem sign name] checks whether a symbol named [name] exists in [sign]. *)
let mem : t -> string -> bool =
  fun sign name -> StrMap.mem name !(sign.sign_symbols)

(** [loaded] stores the signatures of the known (already compiled or currently
    being compiled) modules. An important invariant is that all occurrences of
    a symbol are physically equal, even across signatures). This is ensured by
    making copies of terms when loading an object file. *)
let loaded : t PathMap.t ref = ref PathMap.empty

(* NOTE that the current module is stored in [loaded] so that the symbols
   that it contains can be qualified with the name of the module.
   This behavior was inherited from previous versions of Dedukti. *)

(** [loading] contains the [module_path] of the signatures (or files) that are
    being processed. They are stored in a stack due to dependencies. Note that
    the topmost element corresponds to the current module.  If a [module_path]
    appears twice in the stack, then there is a circular dependency. *)
let loading : Path.t list ref = ref []

(** [current_sign ()] returns the current signature. *)
let current_sign () =
  let mp =
    match !loading with
    | mp :: _ -> mp
    | []      -> assert false
  in
  PathMap.find mp !loaded

(** [new_sym n a] creates a new (private definable) symbol of name [n] and
   type [a]. *)
let new_sym : string -> term -> sym = fun name typ ->
  let path = (current_sign()).sign_path in
  { sym_name = name; sym_type = ref typ; sym_path = path; sym_def = ref None
    ; sym_impl = []; sym_rules = ref []; sym_prop = Defin; sym_expo = Privat
    ; sym_tree = ref Tree_types.empty_dtree }

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let rec link_term t =
    let link_binder b =
      let (x,t) = Bindlib.unbind b in
      Bindlib.unbox (Bindlib.bind_var x (lift (link_term t)))
    in
    match unfold t with
    | Vari(_)     -> t
    | Type        -> t
    | Kind        -> t
    | Symb(s)     -> Symb(link_symb s)
    | Prod(a,b)   -> Prod(link_term a, link_binder b)
    | Abst(a,t)   -> Abst(link_term a, link_binder t)
    | LLet(a,t,u) -> LLet(link_term a, link_term t, link_binder u)
    | Appl(t,u)   -> Appl(link_term t, link_term u)
    | Meta(_,_)   -> assert false
    | Patt(i,n,m) -> Patt(i, n, Array.map link_term m)
    | TEnv(t,m)   -> TEnv(t, Array.map link_term m)
    | Wild        -> t
    | TRef(_)     -> t
  and link_rule r =
    let lhs = List.map link_term r.lhs in
    let (xs, rhs) = Bindlib.unmbind r.rhs in
    let rhs = lift (link_term rhs) in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs rhs) in
    {r with lhs ; rhs}
  and link_symb s =
    if s.sym_path = sign.sign_path then s else
    try
      let sign = PathMap.find s.sym_path !loaded in
      try find sign s.sym_name with Not_found -> assert false
    with Not_found -> assert false
  in
  let fn _ (s,_) =
    s.sym_type  := link_term !(s.sym_type);
    s.sym_def   := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn path ls =
    let sign =
      try PathMap.find path !loaded
      with Not_found -> assert false
    in
    let h (n, r) =
      let r = link_rule r in
      let s = find sign n in
      s.sym_rules := !(s.sym_rules) @ [r]
    in
    List.iter h ls
  in
  PathMap.iter gn !(sign.sign_deps);
  sign.sign_builtins := StrMap.map link_symb !(sign.sign_builtins);
  let hn (s,h) = (link_symb s, h) in
  sign.sign_unops := StrMap.map hn !(sign.sign_unops);
  sign.sign_binops := StrMap.map hn !(sign.sign_binops);
  StrMap.iter (fun _ (s, _) -> Tree.update_dtree s) !(sign.sign_symbols);
  sign.sign_quants := SymSet.map link_symb !(sign.sign_quants)

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of our
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
    s.sym_tree := Tree_types.empty_dtree ;
    if s.sym_path <> sign.sign_path then
      (s.sym_type := Kind; s.sym_rules := [])
  in
  let rec unlink_term t =
    let unlink_binder b = unlink_term (snd (Bindlib.unbind b)) in
    let unlink_term_env t =
      match t with
      | TE_Vari(_) -> ()
      | _          -> assert false (* Should not happen, matching-specific. *)
    in
    match unfold t with
    | Vari(_)      -> ()
    | Type         -> ()
    | Kind         -> ()
    | Symb(s)      -> unlink_sym s
    | Prod(a,b)    -> unlink_term a; unlink_binder b
    | Abst(a,t)    -> unlink_term a; unlink_binder t
    | LLet(a,t,u)  -> unlink_term a; unlink_term t; unlink_binder u
    | Appl(t,u)    -> unlink_term t; unlink_term u
    | Meta(_,_)    -> assert false (* Should not happen, uninstantiated. *)
    | Patt(_,_,_)  -> () (* The environment only contains variables. *)
    | TEnv(t,m)    -> unlink_term_env t; Array.iter unlink_term m
    | Wild         -> ()
    | TRef(_)      -> ()
  and unlink_rule r =
    List.iter unlink_term r.lhs;
    let (_, rhs) = Bindlib.unmbind r.rhs in
    unlink_term rhs
  in
  let fn _ (s,_) =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn _ ls = List.iter (fun (_, r) -> unlink_rule r) ls in
  PathMap.iter gn !(sign.sign_deps);
  StrMap.iter (fun _ s -> unlink_sym s) !(sign.sign_builtins);
  StrMap.iter (fun _ (s,_) -> unlink_sym s) !(sign.sign_unops);
  StrMap.iter (fun _ (s,_) -> unlink_sym s) !(sign.sign_binops);
  SymSet.iter unlink_sym !(sign.sign_quants)

(** [add_symbol sign sym_expo sym_prop s a impl] creates a fresh symbol with
    name [s.elt] (which should not already be used in [sign]) and with the
    type [a], in the signature [sign].
    The exposition is [sym_expo] and the property is [sym_prop].
    The list [impl] tells which arguments is implicit.
    The created symbol is returned. *)
let add_symbol : t -> expo -> prop -> strloc -> term -> bool list -> sym =
    fun sign sym_expo sym_prop s a impl ->
  (* Check for metavariables in the symbol type. *)
  if Basics.has_metas true a then
    fatal s.pos "The type of [%s] contains metavariables" s.elt;
  (* We minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  let sym_impl = List.rev (rem_false (List.rev impl)) in
  (* Add the symbol. *)
  let sym =
    { sym_name = s.elt ; sym_type = ref a ; sym_path = sign.sign_path
    ; sym_def = ref None ; sym_impl ; sym_rules = ref [] ; sym_prop
    ; sym_expo ; sym_tree = ref Tree_types.empty_dtree }
  in
  sign.sign_symbols := StrMap.add s.elt (sym, s.pos) !(sign.sign_symbols); sym

(** [write sign fname] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit = fun sign fname ->
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign; Marshal.to_channel oc sign [Marshal.Closures];
         close_out oc; exit 0
  | i -> ignore (Unix.waitpid [] i)

(** NOTE [Unix.fork] is used to safely [unlink] and write an object file,
    while preserving a valid copy of the written signature in the parent
    process. *)

(** [read fname] reads a signature from the object file [fname]. Note that the
    file can only be read properly if it was build with the same binary as the
    one being evaluated. If this is not the case, the program gracefully fails
    with an error message. *)
let read : string -> t = fun fname ->
  let ic = open_in fname in
  let sign =
    try
      let sign = Marshal.from_channel ic in
      close_in ic; sign
    with Failure _ ->
      close_in ic;
      fatal_no_pos "File [%s] is incompatible with current binary...\n" fname
  in
  (* Timed references need reset after unmarshaling (see [Timed] doc). *)
  let reset_timed_refs sign =
    unsafe_reset sign.sign_symbols;
    unsafe_reset sign.sign_deps;
    unsafe_reset sign.sign_builtins;
    unsafe_reset sign.sign_unops;
    unsafe_reset sign.sign_binops;
    let rec reset_term t =
      let reset_binder b = reset_term (snd (Bindlib.unbind b)) in
      match unfold t with
      | Vari(_)     -> ()
      | Type        -> ()
      | Kind        -> ()
      | Symb(s)     -> shallow_reset_sym s
      | Prod(a,b)   -> reset_term a; reset_binder b
      | Abst(a,t)   -> reset_term a; reset_binder t
      | LLet(a,t,u) -> reset_term a; reset_term t; reset_binder u
      | Appl(t,u)   -> reset_term t; reset_term u
      | Meta(_,_)   -> assert false
      | Patt(_,_,m) -> Array.iter reset_term m
      | TEnv(_,m)   -> Array.iter reset_term m
      | Wild        -> ()
      | TRef(r)     -> unsafe_reset r; Option.iter reset_term !r
    and reset_rule r =
      List.iter reset_term r.lhs;
      reset_term (snd (Bindlib.unmbind r.rhs))
    and shallow_reset_sym s =
      unsafe_reset s.sym_type;
      unsafe_reset s.sym_def;
      unsafe_reset s.sym_rules
    in
    let reset_sym s =
      shallow_reset_sym s;
      reset_term !(s.sym_type);
      Option.iter reset_term !(s.sym_def);
      List.iter reset_rule !(s.sym_rules)
    in
    StrMap.iter (fun _ (s,_) -> reset_sym s) !(sign.sign_symbols);
    StrMap.iter (fun _ (s,_) -> shallow_reset_sym s) !(sign.sign_binops);
    StrMap.iter (fun _ s -> shallow_reset_sym s) !(sign.sign_builtins);
    let fn (_,r) = reset_rule r in
    PathMap.iter (fun _ -> List.iter fn) !(sign.sign_deps);
    sign
  in
  reset_timed_refs sign

(** NOTE here, we rely on the fact that a marshaled closure can only be read
    by processes running the same binary as the one that produced it. *)

(** [add_rule sign sym r] adds the new rule [r] to the symbol [sym].  When the
    rule does not correspond to a symbol of signature [sign],  it is stored in
    its dependencies. *)
let add_rule : t -> sym -> rule -> unit = fun sign sym r ->
  sym.sym_rules := !(sym.sym_rules) @ [r];
  if sym.sym_path <> sign.sign_path then
    let m =
      try PathMap.find sym.sym_path !(sign.sign_deps)
      with Not_found -> assert false
    in
    let m = (sym.sym_name, r) :: m in
    sign.sign_deps := PathMap.add sym.sym_path m !(sign.sign_deps)

(** [add_builtin sign s sym] binds the builtin name [s] to [sym] (in the
    signature [sign]). The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign s sym ->
  sign.sign_builtins := StrMap.add s sym !(sign.sign_builtins)

(** [add_unop sign s sym] binds the unary operator [s] to [sym] in [sign].
    If [s] was previously bound, the previous binding is discarded. *)
let add_unop : t -> string -> (sym * unop) -> unit = fun sign s sym ->
  sign.sign_unops := StrMap.add s sym !(sign.sign_unops)

(** [add_binop sign s sym] binds the binary operator [s] to [sym] in [sign].
    If [s] was previously bound, the previous binding is discarded. *)
let add_binop : t -> string -> (sym * binop) -> unit = fun sign s sym ->
  sign.sign_binops := StrMap.add s sym !(sign.sign_binops)

(** [add_ident sign id] add the declared identifier [id] to [sign]. *)
let add_ident : t -> string -> unit = fun sign id ->
  sign.sign_idents := StrSet.add id !(sign.sign_idents)

(** [add_quant sign sym] add the quantifier [sym] to [sign]. *)
let add_quant : t -> sym -> unit = fun sign sym ->
  sign.sign_quants := SymSet.add sym !(sign.sign_quants)

(** [dependencies sign] returns an association list containing (the transitive
    closure of) the dependencies of the signature [sign].  Note that the order
    of the list gives one possible loading order for the signatures. Note also
    that [sign] itself appears at the end of the list. *)
let rec dependencies : t -> (Path.t * t) list = fun sign ->
  (* Recursively compute dependencies for the immediate dependencies. *)
  let fn p _ l = dependencies (PathMap.find p !loaded) :: l in
  let deps = PathMap.fold fn !(sign.sign_deps) [[(sign.sign_path, sign)]] in
  (* Minimize and put everything together. *)
  let rec minimize acc deps =
    let not_here (p,_) =
      let has_p = List.exists (fun (q,_) -> p = q) in
      not (List.exists has_p acc)
    in
    match deps with
    | []      -> List.rev acc
    | d::deps -> minimize ((List.filter not_here d) :: acc) deps
  in
  List.concat (minimize [] deps)
