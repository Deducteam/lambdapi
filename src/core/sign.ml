(** Signature for symbols. *)

open Lplib open Extra
open Common open Error open Pos
open Timed
open Term

(** Data associated to inductive type symbols. *)
type ind_data =
  { ind_cons : sym list (** Constructors. *)
  ; ind_prop : sym      (** Induction principle. *)
  ; ind_nb_params : int (** Number of parameters. *)
  ; ind_nb_types : int  (** Number of mutually defined types. *)
  ; ind_nb_cons : int   (** Number of constructors. *) }

(** Data associated to a symbol defined in another file. *)
type sym_data =
  { rules : rule list
  ; nota : float notation option }

(** Data associated to a dependency. *)
type dep_data =
  { dep_symbols : sym_data StrMap.t
  ; dep_open : bool }

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { sign_symbols  : sym StrMap.t ref
  ; sign_path     : Path.t
  ; sign_deps     : dep_data Path.Map.t ref
  ; sign_builtins : sym StrMap.t ref
  ; sign_ind      : ind_data SymMap.t ref
  ; sign_cp_pos   : cp_pos list SymMap.t ref }

(* NOTE the [deps] field contains a map binding the external modules on
   which the current signature depends to an association list mapping symbols
   to additional rules defined in the current signature. *)

(** The empty signature. WARNING: to be used for creating ghost signatures
   only. Use Sig_state functions otherwise. It's a thunk to force the creation
   of a new record on each call (and avoid unwanted sharing). *)
let dummy : unit -> t = fun () ->
  { sign_symbols = ref StrMap.empty; sign_path = []
  ; sign_deps = ref Path.Map.empty; sign_builtins = ref StrMap.empty
  ; sign_ind = ref SymMap.empty; sign_cp_pos = ref SymMap.empty }

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> sym =
  fun sign name -> StrMap.find name !(sign.sign_symbols)

(** [mem sign name] checks whether a symbol named [name] exists in [sign]. *)
let mem : t -> string -> bool =
  fun sign name -> StrMap.mem name !(sign.sign_symbols)

(** [loaded] stores the signatures of the known (already compiled or currently
    being compiled) modules. An important invariant is that all occurrences of
    a symbol are physically equal, even across signatures). This is ensured by
    making copies of terms when loading an object file. *)
let loaded : t Path.Map.t ref = ref Path.Map.empty

(** [find_sym path name] returns the symbol identified by [path] and [name]
    in the known modules (already compiled or currently being compiled) *)
let find_sym : Path.t -> string -> sym = fun path name ->
 find (Path.Map.find path !loaded) name

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

(** Signature for symbols introduced by Lambdapi and not the user
    (e.g. unification/coercion rules, strings) and always loaded. *)
module Ghost = struct

  let path = Path.ghost "ghost"

  let sign =
    let sign = { (dummy()) with sign_path = path } in
    loaded := Path.Map.add path sign !loaded;
    sign

  let find s = StrMap.find s !(sign.sign_symbols)

  (** [iter f] iters function [f] on ghost symbols. *)
  let iter : (sym -> unit) -> unit = fun f ->
    StrMap.iter (fun _ s -> f s) !(sign.sign_symbols)

end

(** [link sign] establishes physical links to the external symbols. *)
let link : t -> unit = fun sign ->
  let link_symb s =
    if s.sym_path = sign.sign_path then s
    else
      try find (Path.Map.find s.sym_path !loaded) s.sym_name
      with Not_found ->
        if s.sym_path = Ghost.path
           && String.is_string_literal s.sym_name then
          begin
            Ghost.sign.sign_symbols :=
              StrMap.add s.sym_name s !(Ghost.sign.sign_symbols);
            s
          end
        else assert false
  in
  let link_term mk_Appl =
    let rec link_term t =
      match unfold t with
      | Type
      | Kind
      | Vari _ -> t
      | Symb s -> mk_Symb(link_symb s)
      | Prod(a,b) -> mk_Prod(link_term a, binder link_term b)
      | Abst(a,b) -> mk_Abst(link_term a, binder link_term b)
      | LLet(a,t,b) -> mk_LLet(link_term a, link_term t, binder link_term b)
      | Appl(a,b)   -> mk_Appl(link_term a, link_term b)
      | Patt(i,n,ts)-> mk_Patt(i, n, Array.map link_term ts)
      | Bvar _ -> assert false
      | Meta _ -> assert false
      | Plac _ -> assert false
      | Wild -> assert false
      | TRef _ -> assert false
    in link_term
  in
  let link_lhs = link_term mk_Appl_not_canonical
  and link_term = link_term mk_Appl in
  let link_rule r =
    let lhs = List.map link_lhs r.lhs in
    let rhs = link_term r.rhs in
    {r with lhs ; rhs}
  in
  let f _ s =
    s.sym_type := link_term !(s.sym_type);
    s.sym_def := Option.map link_term !(s.sym_def);
    s.sym_rules := List.map link_rule !(s.sym_rules);
    Tree.update_dtree s []
  in
  StrMap.iter f !(sign.sign_symbols);
  let f mp {dep_symbols=sm; _} =
    if sm <> Extra.StrMap.empty then
      let sign =
        try Path.Map.find mp !loaded with Not_found -> assert false in
      let g n sd =
        let s = try find sign n with Not_found -> assert false in
        s.sym_rules := !(s.sym_rules) @ List.map link_rule sd.rules;
        Option.iter (fun n -> s.sym_nota := n) sd.nota;
        Tree.update_dtree s []
      in
      StrMap.iter g sm
  in
  Path.Map.iter f !(sign.sign_deps);
  sign.sign_builtins := StrMap.map link_symb !(sign.sign_builtins);
  let link_ind_data i =
    { ind_cons = List.map link_symb i.ind_cons;
      ind_prop = link_symb i.ind_prop; ind_nb_params = i.ind_nb_params;
      ind_nb_types = i.ind_nb_types; ind_nb_cons = i.ind_nb_cons }
  in
  let f s i m = SymMap.add (link_symb s) (link_ind_data i) m in
  sign.sign_ind := SymMap.fold f !(sign.sign_ind) SymMap.empty;
  let link_cp_pos (pos,l,r,p,l_p) =
    pos, link_lhs l, link_term r, p, link_lhs l_p in
  let f s cps m = SymMap.add (link_symb s) (List.map link_cp_pos cps) m in
  sign.sign_cp_pos := SymMap.fold f !(sign.sign_cp_pos) SymMap.empty

let link s = Debug.(record_time Sharing (fun () -> link s))

(** [unlink sign] removes references to external symbols (and thus signatures)
    in the signature [sign]. This function is used to minimize the size of
    object files, by preventing a recursive inclusion of all the dependencies.
    Note however that [unlink] processes [sign] in place, which means that the
    signature is invalidated in the process. *)
let unlink : t -> unit = fun sign ->
  let unlink_sym s =
    s.sym_dtree := Tree_type.empty_dtree;
    if s.sym_path <> sign.sign_path then
      (s.sym_type := mk_Kind; s.sym_rules := [])
  in
  let rec unlink_term t =
    match unfold t with
    | Symb s -> unlink_sym s
    | Prod(a,b)
    | Abst(a,b) -> unlink_term a; unlink_term (snd(unbind b))
    | LLet(a,t,b) -> unlink_term a; unlink_term t; unlink_term (snd(unbind b))
    | Appl(a,b) -> unlink_term a; unlink_term b
    | Meta _ -> assert false
    | Plac _ -> assert false
    | Wild   -> assert false
    | TRef _ -> assert false
    | Bvar _ -> assert false
    | Vari _
    | Patt _
    | Type
    | Kind -> ()
  in
  let unlink_rule r =
    List.iter unlink_term r.lhs;
    unlink_term r.rhs
  in
  let f _ s =
    unlink_term !(s.sym_type);
    Option.iter unlink_term !(s.sym_def);
    List.iter unlink_rule !(s.sym_rules)
  in
  StrMap.iter f !(sign.sign_symbols);
  let f _ {dep_symbols=sm; _} =
    StrMap.iter (fun _ sd -> List.iter unlink_rule sd.rules) sm in
  Path.Map.iter f !(sign.sign_deps);
  StrMap.iter (fun _ s -> unlink_sym s) !(sign.sign_builtins);
  let unlink_ind_data i =
    List.iter unlink_sym i.ind_cons; unlink_sym i.ind_prop in
  let f s i = unlink_sym s; unlink_ind_data i in
  SymMap.iter f !(sign.sign_ind);
  let unlink_cp_pos (_,l,r,_,l_p) =
    unlink_term l; unlink_term r; unlink_term l_p in
  let f s cps = unlink_sym s; List.iter unlink_cp_pos cps in
  SymMap.iter f !(sign.sign_cp_pos)

let add_symbol_callback = Stdlib.ref (fun _ -> ())
let add_rules_callback = Stdlib.ref (fun _ _ -> ())

(** [add_symbol sign expo prop mstrat opaq name pos typ impl notation] adds in
    the signature [sign] a symbol with name [name], exposition [expo],
    property [prop], matching strategy [strat], opacity [opaq], type [typ],
    implicit arguments [impl], no notation, no definition and no rules. [name]
    should not already be used in [sign]. [pos] is the position of the
    declaration (without its definition). The created symbol is returned. *)
let add_symbol : t -> expo -> prop -> match_strat -> bool -> strloc ->
  popt -> term -> bool list -> sym =
  fun sign sym_expo sym_prop sym_mstrat sym_opaq name pos typ impl ->
  let sym =
    create_sym sign.sign_path sym_expo sym_prop sym_mstrat sym_opaq name pos
      (cleanup typ) (minimize_impl impl)
  in
  sign.sign_symbols := StrMap.add name.elt sym !(sign.sign_symbols);
  if Stdlib.(!Common.Mode.lsp_mod) then Stdlib.(!add_symbol_callback sym) ;
  sym

(** [strip_private sign] removes private symbols from signature [sign]. *)
let strip_private : t -> unit = fun sign ->
  let not_prv sym = not (Term.is_private sym) in
  sign.sign_symbols :=
    StrMap.filter (fun _ s -> not_prv s) !(sign.sign_symbols)

(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit = fun sign fname ->
  (* [Unix.fork] is used to safely [unlink] and write an object file, while
     preserving a valid copy of the written signature in the parent
     process. *)
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign; Marshal.to_channel oc sign [Marshal.Closures];
         close_out oc; Stdlib.(Debug.do_print_time := false); exit 0
  | i -> ignore (Unix.waitpid [] i); Stdlib.(Debug.do_print_time := true)

let write s n = Debug.(record_time Writing (fun () -> write s n))

(** [read fname] reads a signature from the object file [fname]. Note that the
    file can only be read properly if it was build with the same binary as the
    one being evaluated. If this is not the case, the program gracefully fails
    with an error message. *)
(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)
let read : string -> t = fun fname ->
  let ic = open_in fname in
  let sign =
    try
      let sign = Marshal.from_channel ic in
      close_in ic; sign
    with Failure _ ->
      close_in ic;
      fatal_no_pos "File \"%s\" is incompatible with current binary." fname
  in
  (* Timed references need reset after unmarshaling (see [Timed] doc). *)
  unsafe_reset sign.sign_symbols;
  unsafe_reset sign.sign_deps;
  unsafe_reset sign.sign_builtins;
  unsafe_reset sign.sign_ind;
  unsafe_reset sign.sign_cp_pos;
  let shallow_reset_sym s =
    unsafe_reset s.sym_type;
    unsafe_reset s.sym_def;
    unsafe_reset s.sym_rules;
    (* s.sym_dtree is not reset since it is recomputed. *)
  in
  let rec reset_term t =
    match unfold t with
    | Type
    | Kind
    | Vari _ -> ()
    | Symb s -> shallow_reset_sym s
    | Prod(a,b)
    | Abst(a,b) -> reset_term a; reset_term (snd (unbind b))
    | LLet(a,t,b) -> reset_term a; reset_term t; reset_term (snd(unbind b))
    | Appl(a,b) -> reset_term a; reset_term b
    | Patt(_,_,ts) -> Array.iter reset_term ts
    | Bvar _ -> assert false
    | TRef _ -> assert false
    | Wild -> assert false
    | Meta _ -> assert false
    | Plac _ -> assert false
  in
  let reset_rule r =
    List.iter reset_term r.lhs;
    reset_term r.rhs
  in
  let reset_sym s =
    shallow_reset_sym s;
    reset_term !(s.sym_type);
    Option.iter reset_term !(s.sym_def);
    List.iter reset_rule !(s.sym_rules)
  in
  StrMap.iter (fun _ s -> reset_sym s) !(sign.sign_symbols);
  StrMap.iter (fun _ s -> shallow_reset_sym s) !(sign.sign_builtins);
  let f _ {dep_symbols=sm; _} =
    StrMap.iter (fun _ sd -> List.iter reset_rule sd.rules) sm in
  Path.Map.iter f !(sign.sign_deps);
  let reset_ind i =
    shallow_reset_sym i.ind_prop; List.iter shallow_reset_sym i.ind_cons in
  let f s i = shallow_reset_sym s; reset_ind i in
  SymMap.iter f !(sign.sign_ind);
  let reset_cp_pos (_,l,r,_,l_p) =
    reset_term l; reset_term r; reset_term l_p in
  let f s cps = shallow_reset_sym s; List.iter reset_cp_pos cps in
  SymMap.iter f !(sign.sign_cp_pos);
  sign

let read =
  let open Stdlib in let r = ref (dummy ()) in fun n ->
  Debug.(record_time Reading (fun () -> r := read n)); !r

(** [add_rules sign s rs] adds the new rules [rs] to the symbol [s]. When the
    rules do not correspond to a symbol of signature [sign], they are stored
    in its dependencies. /!\ does not update the decision tree or the critical
    pairs. *)
let add_rules : t -> sym -> rule list -> unit = fun sign s rs ->
  s.sym_rules := !(s.sym_rules) @ rs;
  if s.sym_path <> sign.sign_path then
   begin
    let d = try Path.Map.find s.sym_path !(sign.sign_deps)
            with Not_found -> assert false in
    let f = function
      | None -> Some{rules=rs; nota=None}
      | Some sd -> Some{sd with rules=sd.rules@rs}
    in
    let sm = StrMap.update s.sym_name f d.dep_symbols in
    let d = {d with dep_symbols=sm} in
    sign.sign_deps := Path.Map.add s.sym_path d !(sign.sign_deps)
   end ;
  if Stdlib.(!Common.Mode.lsp_mod) then Stdlib.(!add_rules_callback s rs)

(** [add_rule sign s r] adds the new rule [r] to the symbol [s]. When the rule
    does not correspond to a symbol of signature [sign], it is stored in its
    dependencies. /!\ does not update the decision tree or the critical
    pairs. *)
let add_rule : t -> sym_rule -> unit = fun sign (s,r) ->
  add_rules sign s [r]


(** [add_notation sign sym nota] changes the notation of [s] to [n] in
    the signature [sign]. *)
let add_notation : t -> sym -> float notation -> unit = fun sign s n ->
  s.sym_nota := n;
  if s.sym_path <> sign.sign_path then
    let d = try Path.Map.find s.sym_path !(sign.sign_deps)
             with Not_found -> assert false in
    let f = function
      | None -> Some{rules=[]; nota=Some n}
      | Some sd -> Some{sd with nota=Some n}
    in
    let sm = StrMap.update s.sym_name f d.dep_symbols in
    let d = {d with dep_symbols=sm} in
    sign.sign_deps := Path.Map.add s.sym_path d !(sign.sign_deps)

(** [add_builtin sign name sym] binds the builtin [name] to [sym] in the
    signature [sign]. The previous binding, if any, is discarded. *)
let add_builtin : t -> string -> sym -> unit = fun sign name sym ->
  sign.sign_builtins := StrMap.add name sym !(sign.sign_builtins)

(** [add_inductive sign ind_sym ind_cons ind_prop ind_prop_args] add to [sign]
   the inductive type [ind_sym] with constructors [ind_cons], induction
   principle [ind_prop] with [ind_prop_args] arguments. *)
let add_inductive : t -> sym -> sym list -> sym -> int -> int -> unit =
  fun sign ind_sym ind_cons ind_prop ind_nb_params ind_nb_types ->
  let ind_nb_cons = List.length ind_cons in
  let ind = {ind_cons; ind_prop; ind_nb_params; ind_nb_types; ind_nb_cons} in
  sign.sign_ind := SymMap.add ind_sym ind !(sign.sign_ind)

(** [iterate f sign] applies [f] on [sign] and its dependencies
   recursively. *)
let iterate : (t -> unit) -> t -> unit = fun f sign ->
  let visited = Stdlib.ref Path.Set.empty in
  let rec handle sign =
    Stdlib.(visited := Path.Set.add sign.sign_path !visited);
    f sign;
    let dep path _ =
      if not (Path.Set.mem path Stdlib.(!visited)) then
        handle (Path.Map.find path !loaded)
    in
    Path.Map.iter dep !(sign.sign_deps)
  in handle sign

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
