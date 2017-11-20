open Console
open Terms

(* Representation of a signature (roughly, a set of symbols). *)
type t = { symbols : (string, symbol) Hashtbl.t ; path : string list }

(* [create path] creates an empty signature with module path [path]. *)
let create : string list -> t =
  fun path -> { path ; symbols = Hashtbl.create 37 }

(* [new_static sign name a] creates a new static symbol named [name]  with
   type [a] the signature [sign]. The created symbol is also returned. *)
let new_static : t -> string -> term -> sym =
  fun sign sym_name sym_type ->
    if Hashtbl.mem sign.symbols sym_name then
      wrn "Redefinition of %s.\n" sym_name;
    let sym_path = sign.path in
    let sym = { sym_name ; sym_type ; sym_path } in
    Hashtbl.add sign.symbols sym_name (Sym(sym));
    out 2 "(stat) %s\n" sym_name; sym

(* [new_definable sign name a] creates a new definable symbol (without any
   reduction rule) named [name] with type [a] in the signature [sign]. The
   created symbol is also returned. *)
let new_definable : t -> string -> term -> def =
  fun sign def_name def_type ->
    if Hashtbl.mem sign.symbols def_name then
      wrn "Redefinition of %s.\n" def_name;
    let def_path = sign.path in
    let def_rules = ref [] in
    let def = { def_name ; def_type ; def_rules ; def_path } in
    Hashtbl.add sign.symbols def_name (Def(def));
    out 2 "(defi) %s\n" def_name; def

(* [find sign name] looks for a symbol named [name] in signature [sign] if
   there is one. The exception [Not_found] is raised if there is none. *)
let find : t -> string -> symbol =
  fun sign name -> Hashtbl.find sign.symbols name

(* [write sign file] writes the signature [sign] to the file [fname]. *)
let write : t -> string -> unit =
  fun sign fname ->
    let oc = open_out fname in
    Marshal.to_channel oc sign [Marshal.Closures];
    close_out oc

(* [read fname] reads a signature from the file [fname]. *)
let read : string -> t =
  fun fname ->
    let ic = open_in fname in
    let sign = Marshal.from_channel ic in
    close_in ic; sign

(* [_Symb_find sign name] finds the symbol [s] with the given [name] in [sign]
   and injects the constructor [Symb(s)] into the [bindbox] type.  [Not_found]
   is raised if no such symbol is found. *)
let _Symb_find : t -> string -> tbox = fun sign n ->
  _Symb (find sign n)
