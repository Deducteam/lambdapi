(** Registering and checking builtin symbols. *)

open Lplib open Base open Extra
open Timed
open Common open Error open Pos
open Term
open Sig_state

(** [get ss ~mp ~pos name] returns the symbol mapped to the builtin [name].
   If [mp] is empty (unqualified), it first checks the current signature's path,
   then searches through all other modules. If [mp] is specified (qualified),
   it looks only in that specific module path.
   If the symbol cannot be found then [Fatal] is raised. *)
let get : sig_state -> ?mp:Path.t -> ?pos:popt -> string -> sym = fun ss ?(mp=[]) ?(pos=None) name ->
  match mp with
  | [] ->
    (* Unqualified: search current signature first, then all other paths *)
    begin
      try
        StrMap.find name (Path.Map.find ss.signature.sign_path ss.builtins)
      with Not_found ->
        (* If not found, search through all other paths *)
        let exception Found of sym in
        try
          Path.Map.iter (fun path strmap ->
            if path <> ss.signature.sign_path then
              match StrMap.find_opt name strmap with
              | Some s -> raise (Found s)
              | None -> ()
          ) ss.builtins;
          fatal pos "Unknown builtin symbol %s." name
        with Found s -> s
    end
  | path ->
    (* Qualified: look in the specific path *)
    begin
      try StrMap.find name (Path.Map.find path ss.builtins) with Not_found ->
        fatal pos "Builtin symbol \"%s\" in %a undefined." name Path.pp path
    end

(** Hash-table used to record checking functions for builtins. *)
let htbl : (string, sig_state -> popt -> sym -> unit) Hashtbl.t =
  Hashtbl.create 17

(** [check ss pos name sym] runs the registered check for builtin symbol
   [name] on the symbol [sym] (if such a check has been registered). Note that
   the [bmap] argument is expected to contain the builtin symbols in scope,
   and the [pos] argument is used for error reporting. *)
let check : sig_state -> popt -> string -> sym -> unit =
  fun ss pos name sym ->
  try Hashtbl.find htbl name ss pos sym with Not_found -> ()

(** [register name check] registers the checking function [check], for the
   builtin symbols named [name]. When the check is run, [check] receives as
   argument a position for error reporting as well as the map of every builtin
   symbol in scope. It is expected to raise the [Fatal] exception to signal an
   error. Note that this function should not be called using a [name] for
   which a check has already been registered. *)
let register : string -> (sig_state -> popt -> sym -> unit) -> unit =
  fun name check ->
  if Hashtbl.mem htbl name then assert false;
  Hashtbl.add htbl name check

(** [register_expected_type name build pp] registers a checking function that
   checks the type of a symbol defining the builtin [name] against a type
   constructed using the given [build] function. *)
let register_expected_type
    : term eq -> term pp -> string -> (sig_state -> popt -> term) -> unit =
  fun eq pp name fn ->
  let check ss pos sym =
    let expected = fn ss pos in
    if not (eq !(sym.sym_type) expected) then
      fatal pos "The type of %s is not of the form %a."
        sym.sym_name pp expected
  in
  register name check
