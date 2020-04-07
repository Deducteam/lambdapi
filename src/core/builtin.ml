(** Builtin symbols. *)

open Extra
open Timed
open Terms
open Console
open Print
open Pos

(** Builtin symbols map. *)
type map = sym StrMap.t

(** [get pos map name] returns the symbol mapped to the “builtin symbol” named
    [name] in the map [map], which should contain all the builtin symbols that
    are in scope. If the symbol cannot be found then [Fatal] is raised. *)
let get : popt -> map -> string -> sym = fun pos map name ->
  try StrMap.find name map with Not_found ->
    fatal pos "Builtin symbol [%s] undefined." name

(** Simple interface to register checks on builtin symbols. *)
module Check :
  sig
    (** [check pos bmap name sym] runs the registered check for builtin symbol
        [name] on the symbol [sym] (if such a check has been registered). Note
        that the [bmap] argument is expected to contain the builtin symbols in
        scope, and the [pos] argument is used for error reporting. *)
    val check : popt -> map -> string -> sym -> unit

    (** [register name check] registers the checking function [check], for the
        builtin symbols named [name]. When the check is run,  [check] receives
        as argument a position for error reporting as well as the map of every
        builtin symbol in scope. It is expected to raise the [Fatal] exception
        to signal an error. Note that this function should not be called using
        a [name] for which a check has already been registered. *)
    val register : string -> (popt -> map -> sym -> unit) -> unit

    (** [register_expected_type name build] registers a checking function that
        checks the type of a symbol defining the builtin [name] against a type
        constructed using the given [build] function. *)
    val register_expected_type : string -> (popt -> map -> term) -> unit
  end =
  struct
    let htbl = Hashtbl.create 17

    let check pos bmap name sym =
      try (Hashtbl.find htbl name) pos bmap sym with Not_found -> ()

    let register name check =
      if Hashtbl.mem htbl name then assert false;
      Hashtbl.add htbl name check

    let register_expected_type name fn =
      let check pos map sym =
        let expected = fn pos map in
        if not (Eval.eq_modulo [] !(sym.sym_type) expected) then
          fatal pos "The type of [%s] is not of the form [%a]."
            sym.sym_name pp expected
      in
      register name check
  end
