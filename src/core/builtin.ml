(** Registering and checking builtin symbols. *)

open Lplib open Base open Extra
open Timed
open Common open Error open Pos
open Term
open Sig_state
open Sign

(** [get ss pos path name] returns the symbol mapped to the builtin [name] in
    [path] if any. If the symbol cannot be found then [Fatal] is raised. *)
let get : sig_state -> popt -> Path.t -> string -> sym =
  fun ss pos p s ->
  match p with
  | [] -> (* Symbol in scope. *)
      begin
        try StrMap.find s ss.builtins
        with Not_found -> fatal pos "Unknown builtin %s." s
      end
  | [m] when StrMap.mem m ss.alias_path -> (* Aliased module path. *)
      begin
        (* The signature must be loaded (alias is mapped). *)
        let sign =
          try Path.Map.find (StrMap.find m ss.alias_path) !loaded
          with _ -> assert false (* Should not happen. *)
        in
        (* Look for the symbol. *)
        try StrMap.find s !(sign.sign_builtins) with Not_found ->
          fatal pos "Unknown builtin %a.%s." Path.pp p s
      end
  | _  -> (* Fully-qualified symbol. *)
      begin
        (* Check that the signature was required (or is the current one). *)
        if p <> ss.signature.sign_path then
          if not (Path.Map.mem p !(ss.signature.sign_deps)) then
            fatal pos "No module %a required." Path.pp p;
        (* The signature must have been loaded. *)
        let sign =
          try Path.Map.find p !loaded
          with Not_found -> assert false (* Should not happen. *)
        in
        (* Look for the symbol. *)
        try StrMap.find s !(sign.sign_builtins) with Not_found ->
          fatal pos "Unknown builtin %a.%s." Path.pp p s
      end

(** [get_opt ss name] returns [Some s] where [s] is the symbol mapped to
   the builtin [name], and [None] otherwise. *)
let get_opt : sig_state -> string -> sym option = fun ss name ->
  try Some (StrMap.find name ss.builtins) with Not_found -> None

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
