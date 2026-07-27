(** Verbose level and loggers management. *)

open Timed
open Lplib open Base open Extra

(** [out_fmt] main output formatter. *)
let out_fmt = Stdlib.ref Format.std_formatter

(** Current verbosity level. *)
let verbose = ref 1

(** Default verbosity level (may be set with command line arguments). *)
let default_verbose = Stdlib.ref 1

(** [set_default_verbose i] sets the default verbosity level to [i]. *)
let set_default_verbose : int -> unit = fun i ->
  Stdlib.(default_verbose := i); verbose := i

(** [out lvl fmt] prints an output message using the format [fmt], but only if
    [lvl] is strictly greater than the current verbosity level.  Note that the
    output channel is automatically flushed if logging modes are enabled. *)
let out : int -> 'a outfmt -> 'a = fun lvl fmt ->
  Color.update_with_color Stdlib.(!out_fmt);
  let out = Format.(if lvl > !verbose then ifprintf else fprintf) in
  out Stdlib.(!out_fmt) (fmt ^^ "@.")

(** List of registered boolean flags, with their default values. *)
let boolean_flags : (bool * bool ref) StrMap.t Stdlib.ref =
  Stdlib.ref StrMap.empty

(** [register_flag id d] registers a new boolean flag named [id], with default
    value of [d]. Note the name should not have been used previously. *)
let register_flag : string -> bool -> bool ref = fun id default ->
  if StrMap.mem id Stdlib.(!boolean_flags) then
    invalid_arg "Console.register_flag: already registered";
  let r = ref default in
  Stdlib.(boolean_flags := StrMap.add id (default, r) !boolean_flags); r

(** [set_flag id b] sets the value of the flag named [id] to be [b], or raises
    [Not_found] if no flag with this name was registered. *)
let set_flag : string -> bool -> unit = fun id b ->
  snd (StrMap.find id Stdlib.(!boolean_flags)) := b

(** [reset_default ()] resets the verbosity level and the state of the loggers
    to their default value (configurable by the user with command line flags).
    The boolean flags are also reset to their default values. *)
let reset_default : unit -> unit = fun () ->
  (* Reset verbosity level. *)
  verbose := Stdlib.(!default_verbose);
  (* Reset debugging flags. *)
  Logger.reset_loggers ();
  (* Reset flags to their default values. *)
  let reset _ (default, r) = r := default in
  StrMap.iter reset Stdlib.(!boolean_flags)

(** Module to manipulate imperative state of the typechecker. *)
module State = struct
  (** Settings used to compile files. *)
  type t =
    { verbose: int
    (** Verbosity level. *)
    ; loggers: string
    (** Loggers enabled. *)
    ; bflags: bool StrMap.t
    (** Boolean flags. *) }

  (** Stack of saved state for verbosity, loggers and boolean flags. *)
  let saved : t list ref = ref []
  (* NOTE: could be hidden in the signature declaration. *)

  (** [push ()] saves the current state of [verbose], the loggers, and the
      boolean flags, pushing it to the stack. *)
  let push : unit -> unit = fun () ->
    let verbose = !verbose in
    let loggers = Logger.get_activated_loggers () in
    let bflags : bool StrMap.t =
      let fn (_,r) = !r in
      StrMap.map fn Stdlib.(!boolean_flags)
    in
    saved := {verbose; loggers; bflags} :: !saved

  (** [apply st] restores the setting in [st]. *)
  let apply : t -> unit =
    fun {verbose=v; loggers=l; bflags=f} ->
    (* Reset verbosity level. *)
    verbose := v;
    (* Reset debugging flags. *)
    Logger.reset_loggers ~default:l ();
    (* Reset boolean flags. *)
    let reset k (_,r) =
      try r := StrMap.find k f
      with Not_found -> ()
    in
    StrMap.iter reset Stdlib.(!boolean_flags)

  (** [pop ()] restores the settings saved by [push_state], removing it
      from [saved_state]. *)
  let pop : unit -> unit = fun () ->
    let e =
      match !saved with
      | [] -> failwith "[Console.pop_state] not well-bracketed."
      | e::s -> saved := s; e
    in
    apply e
end

(** [lsp_mod] indicates whether we are executing the LSP server.
    Constants and rules are indexed automatically only in LSP mode
    and not in check mode *)
let lsp_mod = Stdlib.ref false
