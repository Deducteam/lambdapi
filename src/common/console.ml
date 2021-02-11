(** Flag management. *)

open Timed
open Lplib.Base
open Lplib.Extra
open Debug

(** Current verbosity level. *)
let verbose = ref 1

(** Default verbosity level (may be set with command line arguments). *)
let default_verbose = Stdlib.ref 1

(** [set_default_verbose i] sets the default verbosity level to [i]. *)
let set_default_verbose : int -> unit = fun i ->
  Stdlib.(default_verbose := i); verbose := i

(** [out lvl fmt] prints an output message using the format [fmt], but only if
    [lvl] is strictly greater than the current verbosity level.  Note that the
    output channel is automatically flushed,  and  the message is displayed in
    magenta (and not default terminal color) if logging modes are enabled. *)
let out : int -> 'a outfmt -> 'a = fun lvl fmt ->
  let fmt = if !log_enabled then fmt else fmt ^^ "%!" in
  if lvl > !verbose then Format.ifprintf Stdlib.(!out_fmt) fmt
  else Format.fprintf Stdlib.(!out_fmt) fmt

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
  log_enabled := false;
  let reset l =
    let v = String.contains Stdlib.(!default_loggers) l.logger_key in
    l.logger_enabled := v; if v then log_enabled := true;
  in
  List.iter reset Stdlib.(!loggers);
  (* Reset flags to their default values. *)
  let reset _ (default, r) = r := default in
  StrMap.iter reset Stdlib.(!boolean_flags)

(** Module to manipulate imperative state of the typechecker. *)
module State = struct
  (** Settings used to compile files. *)
  type t =
    { verbose: int
    (** Verbosity level. *)
    ; loggers: (char * bool) list
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
    let loggers =
      let fn l = (l.logger_key, !(l.logger_enabled)) in
      List.map fn Stdlib.(!loggers)
    in
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
    log_enabled := false;
    let reset logger =
      let v = try List.assoc logger.logger_key l with Not_found -> false in
      logger.logger_enabled := v; if v then log_enabled := true;
    in
    List.iter reset Stdlib.(!loggers);
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
