(** Signature for symbols. *)

open! Lplib
open Lplib.Extra

open Common
open Error
open Pos
open Timed
open Term
open Parsing.Syntax
open Tags

(** Representation of an inductive type *)
type inductive =
  { ind_cons  : sym list  (** List of constructors                 *)
  ; ind_prop  : sym       (** Induction principle on propositions. *) }

(** Notation properties of symbols. They are linked to symbols to provide
    syntax extensions to these symbols. These syntax extensions concern both
    parsing and printing. *)
type notation =
  | Prefix of unop (** Prefix (or unary) operator, such as [!] in [! x]. *)
  | Infix of binop (** Infix (or binary) operator, such as [+] in [a + b]. *)
  | Zero (** The numeral zero, that is [0]. *)
  | Succ (** Successor, for numerals such as [42]. *)
  | Quant (** Quantifier, such as [fa] in [`fa x, t]. *)

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : (sym * Pos.popt) StrMap.t ref
  ; sign_path      : Path.t
  ; sign_deps     : (string * rule) list Path.Map.t ref
  ; sign_builtins : sym StrMap.t ref
  ; sign_notations: notation SymMap.t ref
    (** Maps symbols to their syntax properties if they have some. *)
  ; sign_ind      : inductive SymMap.t ref }

(* NOTE the [deps] field contains a hashtable binding the external modules on
   which the current signature depends to an association list mapping symbols
   to additional rules defined in the current signature. *)

(** The empty signature. It's a thunk to force the creation of a new record on
    each call (and avoid unwanted sharing). *)
let dummy : unit -> t = fun () ->
  { sign_symbols = ref StrMap.empty; sign_path = []
  ; sign_deps = ref Path.Map.empty; sign_builtins = ref StrMap.empty
  ; sign_notations = ref SymMap.empty; sign_ind = ref SymMap.empty }

(** [create mp] creates an empty signature in the module [mp]. *)
let create : Path.t -> t = fun sign_path ->
  let d = dummy () in { d with sign_path }

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
let loaded : t Path.Map.t ref = ref Path.Map.empty

(* NOTE that the current module is stored in [loaded] so that the symbols that
   it contains can be qualified with the name of the module. This behavior was
   inherited from previous versions of Dedukti. *)

(** [loading] contains the modules that are being processed. They are stored
   in a stack due to dependencies. Note that the topmost element corresponds
   to the current module. If a module appears twice in the stack, then there
   is a circular dependency. *)
let loading : Path.t list ref = ref []

(** [current_sign ()] returns the current signature. *)
let current_sign () = Path.Map.find (List.hd !loading) !loaded

(** [create_sym expo prop opaq name typ impl] creates a new symbol with the
   exposition [expo], property [prop], name [name], type [typ], implicit
   arguments [impl], opacity [opaq]. *)
let create_sym : expo -> prop -> bool -> string -> term -> bool list -> sym =
  fun sym_expo sym_prop sym_opaq sym_name typ sym_impl ->
  let sym_path = (current_sign()).sign_path in
  { sym_expo; sym_path; sym_name; sym_type = ref typ; sym_impl; sym_prop;
    sym_def = ref None; sym_opaq; sym_rules = ref [];
    sym_mstrat = ref Eager; sym_tree = ref Tree_types.empty_dtree }

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
      let sign = Path.Map.find s.sym_path !loaded in
      try find sign s.sym_name with Not_found -> assert false
    with Not_found -> assert false
  in
  let fn _ (s,_) =
    s.sym_type  := link_term !(s.sym_type);
    s.sym_def   := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules)
  in
  StrMap.iter fn !(sign.sign_symbols);
  let gn mp ls =
    let sign =
      try Path.Map.find mp !loaded
      with Not_found -> assert false
    in
    let h (n, r) =
      let r = link_rule r in
      let s = find sign n in
      s.sym_rules := !(s.sym_rules) @ [r]
    in
    List.iter h ls
  in
  Path.Map.iter gn !(sign.sign_deps);
  sign.sign_builtins := StrMap.map link_symb !(sign.sign_builtins);
  let lsy (sym, h) = link_symb sym, h in
  sign.sign_notations :=
    (* Keys of the mapping are linked *)
    SymMap.to_seq !(sign.sign_notations) |>
    Seq.map lsy |> SymMap.of_seq;
  StrMap.iter (fun _ (s, _) -> Tree.update_dtree s) !(sign.sign_symbols);
  let link_inductive i =
    { ind_cons = List.map link_symb i.ind_cons
    ; ind_prop = link_symb i.ind_prop }
  in
  let fn s i m = SymMap.add (link_symb s) (link_inductive i) m in
  sign.sign_ind := SymMap.fold fn !(sign.sign_ind) SymMap.empty

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
  Path.Map.iter gn !(sign.sign_deps);
  StrMap.iter (fun _ s -> unlink_sym s) !(sign.sign_builtins);
  SymMap.iter (fun s _ -> unlink_sym s) !(sign.sign_notations);
  let unlink_inductive i =
    List.iter unlink_sym i.ind_cons; unlink_sym i.ind_prop
  in
  let fn s i = unlink_sym s; unlink_inductive i in
  SymMap.iter fn !(sign.sign_ind)

(** [add_symbol sign expo prop mstrat opaq name typ impl] add in the signature
   [sign] a symbol with name [name], exposition [expo], property [prop],
   matching strategy [strat], opacity [opaq], type [typ], implicit arguments
   [impl], no definition and no rules. [name] should not already be used in
   [sign]. The created symbol is returned. *)
let add_symbol :
      t -> expo -> Tags.prop -> match_strat -> bool -> strloc -> term ->
      bool list -> sym =
  fun sign sym_expo sym_prop sym_mstrat sym_opaq {elt=sym_name;pos} typ
      impl ->
  (* Check for metavariables in the symbol type. *)
  if LibTerm.has_metas true typ then
    fatal pos "The type of %a contains metavariables"
      Parsing.LpLexer.pp_uid sym_name;
  (* We minimize [impl] to enforce our invariant (see {!type:Terms.sym}). *)
  let rec rem_false l = match l with false::l -> rem_false l | _ -> l in
  let sym_impl = List.rev (rem_false (List.rev impl)) in
  (* Add the symbol. *)
  let sym =
    { sym_path = sign.sign_path; sym_name; sym_type = ref (cleanup typ);
      sym_impl; sym_def = ref None; sym_opaq; sym_rules = ref [];
      sym_tree = ref Tree_types.empty_dtree; sym_mstrat = ref sym_mstrat;
      sym_prop; sym_expo }
  in
  sign.sign_symbols := StrMap.add sym_name (sym, pos) !(sign.sign_symbols);
  sym

(** [strip_private sign] removes private symbols from signature [sign]. *)
let strip_private : t -> unit = fun sign ->
  let not_prv sym = not (Term.is_private sym) in
  sign.sign_symbols :=
    StrMap.filter (fun _ s -> not_prv (fst s)) !(sign.sign_symbols);
  sign.sign_notations :=
    Term.SymMap.filter (fun s _ -> not_prv s) !(sign.sign_notations)

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
      fatal_no_pos "File \"%s\" is incompatible with current binary...\n"
        fname
  in
  (* Timed references need reset after unmarshaling (see [Timed] doc). *)
  let reset_timed_refs sign =
    unsafe_reset sign.sign_symbols;
    unsafe_reset sign.sign_deps;
    unsafe_reset sign.sign_builtins;
    unsafe_reset sign.sign_notations;
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
    StrMap.iter (fun _ s -> shallow_reset_sym s) !(sign.sign_builtins);
    SymMap.iter (fun s _ -> shallow_reset_sym s) !(sign.sign_notations);
    let fn (_,r) = reset_rule r in
    Path.Map.iter (fun _ -> List.iter fn) !(sign.sign_deps);
    let shallow_reset_inductive i =
      shallow_reset_sym i.ind_prop;
      List.iter shallow_reset_sym i.ind_cons
    in
    let fn s i = shallow_reset_sym s; shallow_reset_inductive i in
    SymMap.iter fn !(sign.sign_ind);
    sign
  in
  reset_timed_refs sign

(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)

(** [add_rule sign sym r] adds the new rule [r] to the symbol [sym].  When the
    rule does not correspond to a symbol of signature [sign],  it is stored in
    its dependencies. *)
let add_rule : t -> sym -> rule -> unit = fun sign sym r ->
  sym.sym_rules := !(sym.sym_rules) @ [r];
  if sym.sym_path <> sign.sign_path then
    let m =
      try Path.Map.find sym.sym_path !(sign.sign_deps)
      with Not_found -> assert false
    in
    let m = (sym.sym_name, r) :: m in
    sign.sign_deps := Path.Map.add sym.sym_path m !(sign.sign_deps)

(** [add_builtin sign name sym] binds the builtin name [name] to [sym] (in the
    signature [sign]). The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign s sym ->
  sign.sign_builtins := StrMap.add s sym !(sign.sign_builtins);
  match s with
  | "0" -> sign.sign_notations := SymMap.add sym Zero !(sign.sign_notations)
  | "+1" -> sign.sign_notations := SymMap.add sym Succ !(sign.sign_notations)
  | _ -> ()

(** [add_unop sign sym unop] binds the unary operator [unop] to [sym] in
    [sign]. If [unop] was previously bound, the previous binding is
    discarded. *)
let add_unop : t -> sym -> unop -> unit = fun sign sym unop ->
  sign.sign_notations := SymMap.add sym (Prefix unop) !(sign.sign_notations)

(** [add_binop sign sym binop] binds the binary operator [binop] to [sym] in
    [sign]. If [op] was previously bound, the previous binding is
    discarded. *)
let add_binop : t -> sym -> binop -> unit =
  fun sign sym binop ->
  sign.sign_notations := SymMap.add sym (Infix binop) !(sign.sign_notations)

(** [add_quant sign sym] add the quantifier [sym] to [sign]. *)
let add_quant : t -> sym -> unit = fun sign sym ->
  sign.sign_notations := SymMap.add sym Quant !(sign.sign_notations)

(** [add_inductive sign typ ind_cons ind_prop] add the inductive type which
    consists of a type [typ], constructors [ind_cons] and an induction
    principle [ind_prop] to [sign]. *)
let add_inductive : t -> sym -> sym list -> sym -> unit =
  fun sign typ ind_cons ind_prop ->
  let ind = { ind_cons ; ind_prop } in
  sign.sign_ind := SymMap.add typ ind !(sign.sign_ind)

(** [dependencies sign] returns an association list containing (the transitive
    closure of) the dependencies of the signature [sign].  Note that the order
    of the list gives one possible loading order for the signatures. Note also
    that [sign] itself appears at the end of the list. *)
let rec dependencies : t -> (Path.t * t) list = fun sign ->
  (* Recursively compute dependencies for the immediate dependencies. *)
  let fn p _ l = dependencies (Path.Map.find p !loaded) :: l in
  let deps = Path.Map.fold fn !(sign.sign_deps) [[(sign.sign_path, sign)]] in
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
