(** Simple interface to register checks on builtin symbols. *)

open Extra
open Timed
open Terms
open Console
open Pos

(** Builtin symbols map. *)
type map = sym StrMap.t

(** [get pos map name] returns the symbol mapped to the “builtin symbol” named
   [name] i n the map [map], which should contain all the builtin symbols that
   are in scope. If the symbol cannot be found then [Fatal] is raised. *)
let get : popt -> map -> string -> sym = fun pos map name ->
  try StrMap.find name map with Not_found ->
    fatal pos "Builtin symbol [%s] undefined." name

(** Hash-table used to record checking functions for builtins. *)
let htbl = Hashtbl.create 17

(** [check pos bmap name sym] runs the registered check for builtin symbol
   [name] on the symbol [sym] (if such a check has been registered). Note that
   the [bmap] argument is expected to contain the builtin symbols in scope,
   and the [pos] argument is used for error reporting. *)
let check : popt -> map -> string -> sym -> unit = fun pos bmap name sym ->
  try (Hashtbl.find htbl name) pos bmap sym with Not_found -> ()

(** [register name check] registers the checking function [check], for the
   builtin symbols named [name]. When the check is run, [check] receives as
   argument a position for error reporting as well as the map of every builtin
   symbol in scope. It is expected to raise the [Fatal] exception to signal an
   error. Note that this function should not be called using a [name] for
   which a check has already been registered. *)
let register : string -> (popt -> map -> sym -> unit) -> unit
  = fun name check ->
  if Hashtbl.mem htbl name then assert false;
  Hashtbl.add htbl name check

(** [register_expected_type name build pp] registers a checking function that
   checks the type of a symbol defining the builtin [name] against a type
   constructed using the given [build] function. *)
let register_expected_type
    : term eq -> term pp -> string -> (popt -> map -> term) -> unit
  = fun eq pp name fn ->
  let check pos map sym =
    let expected = fn pos map in
    if not (eq !(sym.sym_type) expected) then
      fatal pos "The type of [%s] is not of the form [%a]."
        sym.sym_name pp expected
  in
  register name check
