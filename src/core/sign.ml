(** Signature for symbols. *)

open! Lplib
open Lplib.Extra

open Common
open Error
open Pos
open Timed
open Term

(** Data associated to inductive type symbols. *)
type ind_data =
  { ind_cons : sym list (** Constructors. *)
  ; ind_prop : sym      (** Induction principle. *)
  ; ind_nb_params : int (** Number of parameters. *)
  ; ind_nb_types : int  (** Number of mutually defined types. *)
  ; ind_nb_cons : int   (** Number of constructors. *) }

(** The priority of an infix operator is a floating-point number. *)
type priority = float

(** Notations. *)
type notation =
  | Prefix of priority
  | Infix of Pratter.associativity * priority
  | Zero
  | Succ
  | Quant

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : (sym * Pos.popt) StrMap.t ref
  ; sign_path     : Path.t
  ; sign_deps     : rule list StrMap.t Path.Map.t ref
  (** Maps a path to a list of pairs (symbol name, rule). *)
  ; sign_builtins : sym StrMap.t ref
  ; sign_notations: notation SymMap.t ref
  (** Maps symbols to their notation if they have some. *)
  ; sign_ind      : ind_data SymMap.t ref }

(* NOTE the [deps] field contains a hashtable binding the external modules on
   which the current signature depends to an association list mapping symbols
   to additional rules defined in the current signature. *)

(** The empty signature. WARNING: to be used for creating ghost signatures
   only. Use Sig_state functions otherwise. It's a thunk to force the creation
   of a new record on each call (and avoid unwanted sharing). *)
let dummy : unit -> t = fun () ->
  { sign_symbols = ref StrMap.empty; sign_path = []
  ; sign_deps = ref Path.Map.empty; sign_builtins = ref StrMap.empty
  ; sign_notations = ref SymMap.empty; sign_ind = ref SymMap.empty }

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

(** [current_path ()] returns the current signature path. *)
let current_path : unit -> Path.t =
  fun () -> (Path.Map.find (List.hd !loading) !loaded).sign_path

(** [create_sym expo prop opaq name typ impl] creates a new symbol with the
   exposition [expo], property [prop], name [name], type [typ], implicit
   arguments [impl], opacity [opaq]. *)
let create_sym : expo -> prop -> bool -> string -> term -> bool list -> sym =
  fun sym_expo sym_prop sym_opaq sym_name typ sym_impl ->
  let sym_path = current_path() in
  { sym_expo; sym_path; sym_name; sym_type = ref typ; sym_impl; sym_prop;
    sym_def = ref None; sym_opaq; sym_rules = ref [];
    sym_mstrat = Eager; sym_dtree = ref Tree_type.empty_dtree }

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let rec link_term mk_Appl t =
    let link_binder b =
      let (x,t) = Bindlib.unbind b in
      Bindlib.unbox (Bindlib.bind_var x (lift (link_term mk_Appl t)))
    in
    match unfold t with
    | Vari(_)     -> t
    | Type        -> t
    | Kind        -> t
    | Symb(s)     -> mk_Symb(link_symb s)
    | Prod(a,b)   -> mk_Prod(link_term mk_Appl a, link_binder b)
    | Abst(a,t)   -> mk_Abst(link_term mk_Appl a, link_binder t)
    | LLet(a,t,u) ->
        mk_LLet(link_term mk_Appl a, link_term mk_Appl t, link_binder u)
    | Appl(t,u)   -> mk_Appl(link_term mk_Appl t, link_term mk_Appl u)
    | Meta(_,_)   -> assert false
    | Patt(i,n,m) -> mk_Patt(i, n, Array.map (link_term mk_Appl) m)
    | TEnv(t,m)   -> mk_TEnv(t, Array.map (link_term mk_Appl) m)
    | Wild        -> assert false
    | TRef(_)     -> assert false
  and link_rule r =
    let lhs = List.map (link_term mk_Appl_not_canonical) r.lhs in
    let (xs, rhs) = Bindlib.unmbind r.rhs in
    let rhs = lift (link_term mk_Appl rhs) in
    let rhs = Bindlib.unbox (Bindlib.bind_mvar xs rhs) in
    {r with lhs ; rhs}
  and link_symb s =
    if s.sym_path = sign.sign_path then s else
    try find (Path.Map.find s.sym_path !loaded) s.sym_name
    with Not_found -> assert false
  in
  let f _ (s,_) =
    s.sym_type  := link_term mk_Appl !(s.sym_type);
    s.sym_def   := Option.map (link_term mk_Appl) !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules)
  in
  StrMap.iter f !(sign.sign_symbols);
  let f mp sm =
    let sign = Path.Map.find mp !loaded in
    let g n rs =
      let s = find sign n in
      s.sym_rules := !(s.sym_rules) @ List.map link_rule rs
      (* /!\ The update of s.sym_dtree is not done here but later as a side
         effect of link (dtree update of sign_symbols below) since
         dependencies are recompiled or loaded and, in case a dependency is
         loaded, it is linked too. *)
    in
    StrMap.iter g sm
  in
  Path.Map.iter f !(sign.sign_deps);
  sign.sign_builtins := StrMap.map link_symb !(sign.sign_builtins);
  sign.sign_notations :=
    SymMap.fold (fun s n m -> SymMap.add (link_symb s) n m)
      !(sign.sign_notations) SymMap.empty;
  StrMap.iter (fun _ (s, _) -> Tree.update_dtree s) !(sign.sign_symbols);
  let link_ind_data i =
    { ind_cons = List.map link_symb i.ind_cons;
      ind_prop = link_symb i.ind_prop; ind_nb_params = i.ind_nb_params;
      ind_nb_types = i.ind_nb_types; ind_nb_cons = i.ind_nb_cons }
  in
  let f s i m = SymMap.add (link_symb s) (link_ind_data i) m in
  sign.sign_ind := SymMap.fold f !(sign.sign_ind) SymMap.empty

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of our
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
    s.sym_dtree := Tree_type.empty_dtree ;
    if s.sym_path <> sign.sign_path then
      (s.sym_type := mk_Kind; s.sym_rules := [])
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
  let f _ (s,_) =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter f !(sign.sign_symbols);
  let f _ sm = StrMap.iter (fun _ rs -> List.iter unlink_rule rs) sm in
  Path.Map.iter f !(sign.sign_deps);
  StrMap.iter (fun _ s -> unlink_sym s) !(sign.sign_builtins);
  SymMap.iter (fun s _ -> unlink_sym s) !(sign.sign_notations);
  let unlink_ind_data i =
    List.iter unlink_sym i.ind_cons; unlink_sym i.ind_prop
  in
  let f s i = unlink_sym s; unlink_ind_data i in
  SymMap.iter f !(sign.sign_ind)

(** [add_symbol sign expo prop mstrat opaq name typ impl] adds in the
   signature [sign] a symbol with name [name], exposition [expo], property
   [prop], matching strategy [strat], opacity [opaq], type [typ], implicit
   arguments [impl], no definition and no rules. [name] should not already be
   used in [sign]. The created symbol is returned. *)
let add_symbol :
      t -> expo -> prop -> match_strat -> bool -> strloc -> term ->
      bool list -> sym =
  fun sign sym_expo sym_prop sym_mstrat sym_opaq {elt=sym_name;pos} typ
      impl ->
  let sym =
    { sym_path = sign.sign_path; sym_name; sym_type = ref (cleanup typ);
      sym_impl = minimize_impl impl; sym_def = ref None; sym_opaq;
      sym_rules = ref []; sym_dtree = ref Tree_type.empty_dtree; sym_mstrat;
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
    let f _ sm = StrMap.iter (fun _ rs -> List.iter reset_rule rs) sm in
    Path.Map.iter f !(sign.sign_deps);
    let shallow_reset_ind_data i =
      shallow_reset_sym i.ind_prop;
      List.iter shallow_reset_sym i.ind_cons
    in
    let f s i = shallow_reset_sym s; shallow_reset_ind_data i in
    SymMap.iter f !(sign.sign_ind);
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
    let sm = Path.Map.find sym.sym_path !(sign.sign_deps) in
    let f = function None -> Some [r] | Some rs -> Some (rs @ [r]) in
    let sm = StrMap.update sym.sym_name f sm in
    sign.sign_deps := Path.Map.add sym.sym_path sm !(sign.sign_deps)

(** [add_builtin sign name sym] binds the builtin name [name] to [sym] (in the
    signature [sign]). The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign s sym ->
  sign.sign_builtins := StrMap.add s sym !(sign.sign_builtins);
  match s with
  | "0" -> sign.sign_notations := SymMap.add sym Zero !(sign.sign_notations)
  | "+1" -> sign.sign_notations := SymMap.add sym Succ !(sign.sign_notations)
  | _ -> ()

(** [add_notation sign s n] sets notation of [s] to [n] in [sign]. *)
let add_notation : t -> sym -> notation -> unit = fun sign s n ->
  sign.sign_notations := SymMap.add s n !(sign.sign_notations)

(** [add_inductive sign ind_sym ind_cons ind_prop ind_prop_args] add to [sign]
   the inductive type [ind_sym] with constructors [ind_cons], induction
   principle [ind_prop] with [ind_prop_args] arguments. *)
let add_inductive : t -> sym -> sym list -> sym -> int -> int -> unit =
  fun sign ind_sym ind_cons ind_prop ind_nb_params ind_nb_types ->
  let ind_nb_cons = List.length ind_cons in
  let ind = {ind_cons; ind_prop; ind_nb_params; ind_nb_types; ind_nb_cons} in
  sign.sign_ind := SymMap.add ind_sym ind !(sign.sign_ind)

(** [dependencies sign] returns an association list containing (the transitive
    closure of) the dependencies of the signature [sign].  Note that the order
    of the list gives one possible loading order for the signatures. Note also
    that [sign] itself appears at the end of the list. *)
let rec dependencies : t -> (Path.t * t) list = fun sign ->
  (* Recursively compute dependencies for the immediate dependencies. *)
  let f p _ l = dependencies (Path.Map.find p !loaded) :: l in
  let deps = Path.Map.fold f !(sign.sign_deps) [[(sign.sign_path, sign)]] in
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

(** [ghost_path s] creates a module path that cannot be entered by a user. *)
let ghost_path : string -> Path.t = fun s -> [ ""; s ]
