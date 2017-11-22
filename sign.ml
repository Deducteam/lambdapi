(** Signature for symbols. *)

open Console
open Files
open Terms

(** Representation of a signature. It roughly corresponds to a set of symbols,
    defined in a single module (or file). *)
type t =
  { symbols : (string, symbol) Hashtbl.t
  ; path    : module_path
  ; deps    : (module_path, (string * rule list) list) Hashtbl.t }

(* NOTE the [deps] field contains a hashtable binding the [module_path] of the
   required modules, on which the current signature depends, to an association
   list mapping definable symbols (given in these modules) to additional rules
   (defined in the current signature, for symbols defined elsewhere. *)
   
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
    let def_rules = ref [] in
    let def = { def_name ; def_type ; def_rules ; def_path } in
    Hashtbl.add sign.symbols def_name (Def(def));
    out 2 "(defi) %s\n" def_name; def

(** [find sign name] finds the symbol named [name] in [sign] if it exists, and
    raises the [Not_found] exception otherwise. *)
let find : t -> string -> symbol =
  fun sign name -> Hashtbl.find sign.symbols name

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
