(** Signature for symbols. *)

open Extra
open Timed
open Console
open Files
open Terms
open Syntax
open Pos

(** [builtin builtins name] finds the builtin symbol named [name]
   in [builtins] if it exists, and fails otherwise. *)
let builtin : popt -> sym StrMap.t -> string -> sym =
  fun pos builtins name ->
  try StrMap.find name builtins
  with Not_found -> fatal pos "Builtin symbol [%s] undefined." name

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : (sym * Pos.popt) StrMap.t ref
  ; sign_path     : module_path
  ; sign_deps     : (string * rule) list PathMap.t ref
  ; sign_builtins : sym StrMap.t ref
  ; sign_binops   : (sym * binop) StrMap.t ref }

(* NOTE the [deps] field contains a hashtable binding the [module_path] of the
   external modules on which the current signature depends to an association
   list. This association list then maps definable symbols of the external
   module to additional reduction rules defined in the current signature. *)

(** [create path] creates an empty signature with module path [path]. *)
let create : module_path -> t = fun sign_path ->
  { sign_path; sign_symbols = ref StrMap.empty; sign_deps = ref PathMap.empty
  ; sign_builtins = ref StrMap.empty; sign_binops = ref StrMap.empty }

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

(* NOTE that the current module is stored in [loaded] so that the symbols that
   it contains can be qualified with the name of the module. This behavior was
   inherited from previous versions of Dedukti. *)

(** [loading] contains the [module_path] of the signatures (or files) that are
    being processed. They are stored in a stack due to dependencies. Note that
    the topmost element corresponds to the current module.  If a [module_path]
    appears twice in the stack, then there is a circular dependency. *)
let loading : module_path list ref = ref []

(** [current_sign ()] returns the current signature. *)
let current_sign () =
  let mp =
    match !loading with
    | mp :: _ -> mp
    | []      -> assert false
  in
  PathMap.find mp !loaded

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
    | Symb(s,h)   -> Symb(link_symb s, h)
    | Prod(a,b)   -> Prod(link_term a, link_binder b)
    | Abst(a,t)   -> Abst(link_term a, link_binder t)
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
  sign.sign_binops := StrMap.map hn !(sign.sign_binops)

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of our
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
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
    | Symb(s,_)    -> unlink_sym s
    | Prod(a,b)    -> unlink_term a; unlink_binder b
    | Abst(a,t)    -> unlink_term a; unlink_binder t
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
  StrMap.iter (fun _ (s,_) -> unlink_sym s) !(sign.sign_binops)

(** [add_symbol sign mode name a impl] creates a fresh symbol with name [name]
    (which should not already be used in [sign]) and with the type [a], in the
    signature [sign]. The list [impl] tells whether the first arguments of the
    symbol are set to be implicit. The created symbol is returned. *)
let add_symbol : t -> sym_mode -> strloc -> term -> bool list -> sym =
    fun sign sym_mode s a impl ->
  (* Check for metavariables in the symbol type. *)
  if Basics.has_metas a then
    fatal s.pos "The type of [%s] contains metavariables" s.elt;
  (* We minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  let sym_impl = List.rev (rem_false (List.rev impl)) in
  (* Add the symbol. *)
  let sym =
    { sym_name = s.elt ; sym_type = ref a ; sym_path = sign.sign_path
    ; sym_def = ref None ; sym_impl ; sym_rules = ref [] ; sym_mode
    ; sym_tree = ref Tree_types.empty_dtree }
  in
  sign.sign_symbols := StrMap.add s.elt (sym, s.pos) !(sign.sign_symbols); sym

(** [is_inj s] tells whether the symbol is injective. *)
let is_inj : sym -> bool = fun s -> s.sym_mode <> Defin

(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit = fun sign fname ->
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign; Marshal.to_channel oc sign [Marshal.Closures];
         close_out oc; exit 0
  | i -> ignore (Unix.waitpid [] i)

(* NOTE [Unix.fork] is used to safely [unlink] and write an object file, while
   preserving a valid copy of the written signature in the parent process. *)

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
    unsafe_reset sign.sign_binops;
    let rec reset_term t =
      let reset_binder b = reset_term (snd (Bindlib.unbind b)) in
      match unfold t with
      | Vari(_)     -> ()
      | Type        -> ()
      | Kind        -> ()
      | Symb(s,_)   -> shallow_reset_sym s
      | Prod(a,b)   -> reset_term a; reset_binder b
      | Abst(a,t)   -> reset_term a; reset_binder t
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

(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)

(** [add_rules s r] adds a bunch of rules [r] to its attached symbol to the
    signature [s] and builds decision trees. *)
let add_rules : t -> (sym * pp_hint * rule loc) list -> unit = fun sign rs ->
  (* [add_rule sign sym r] adds the new rule [r] to the symbol [sym].  When
     the rule does not correspond to a symbol of signature [sign], it is
     stored in its dependencies. *)
  let add_rule (s, h, r) =
    out 3 "(rule) %a\n" Print.pp_rule (s,h,r.elt) ;
    s.sym_rules := !(s.sym_rules) @ [r.elt] ;
    if s.sym_path <> sign.sign_path then
      let m =
        try PathMap.find s.sym_path !(sign.sign_deps)
        with Not_found -> assert false in
      let m = (s.sym_name, r.elt) :: m in
      sign.sign_deps := PathMap.add s.sym_path m !(sign.sign_deps) in
  List.iter add_rule rs ;
  let fst3cmp (d, _, _) (e, _, _) = Basics.sym_cmp d e in
  List.sort_uniq fst3cmp rs |> List.iter (fun (x, _, _) -> Dtree.update_dtree x)

(** [add_builtin sign name sym] binds the builtin name [name] to [sym] (in the
    signature [sign]). The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign s sym ->
  sign.sign_builtins := StrMap.add s sym !(sign.sign_builtins)

(** [add_binop sign op sym] binds the binary operator [op] to [sym] in [sign].
    If [op] was previously bound, the previous binding is discarded. *)
let add_binop : t -> string -> (sym * binop) -> unit = fun sign s sym ->
  sign.sign_binops := StrMap.add s sym !(sign.sign_binops)

(** [dependencies sign] returns an association list containing (the transitive
    closure of) the dependencies of the signature [sign].  Note that the order
    of the list gives one possible loading order for the signatures. Note also
    that [sign] itself appears at the end of the list. *)
let rec dependencies : t -> (module_path * t) list = fun sign ->
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
