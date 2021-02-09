(** Output and debugging utilities. *)

open Timed
open Lplib.Extra

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [color] tells whether colors can be used in the output. *)
let color : bool Stdlib.ref = Stdlib.ref true

(** Format transformers (colors). *)
let colorize k fmt =
  if Stdlib.(!color) then
    "\027[" ^^ k ^^ "m" ^^ fmt ^^ "\027[0m%!"
  else fmt

let red fmt = colorize "31" fmt
let gre fmt = colorize "32" fmt
let yel fmt = colorize "33" fmt
let blu fmt = colorize "34" fmt
let mag fmt = colorize "35" fmt
let cya fmt = colorize "36" fmt

(** [r_or_g cond fmt] colors the format [fmt] in green if [cond] is [true] and
    in red otherwise. *)
let r_or_g cond = if cond then gre else red

(** [out_fmt] main output formatter. *)
let out_fmt = Stdlib.ref Format.std_formatter

(** [err_fmt] warning/error output formatter. *)
let err_fmt = Stdlib.ref Format.err_formatter

(** [no_wrn] disables warnings when set to [true]. *)
let no_wrn = Stdlib.ref false

(** [wrn popt fmt] prints a yellow warning message with [Format] format [fmt].
    Note that the output buffer is flushed by the function, and that output is
    prefixed with the position [popt] if given. A newline is automatically put
    at the end of the message as well. *)
let wrn : Pos.popt -> 'a outfmt -> 'a = fun pos fmt ->
  let open Stdlib in
  let fprintf = if !no_wrn then Format.ifprintf else Format.fprintf in
  match pos with
  | None    -> fprintf !err_fmt (yel (fmt ^^ "\n"))
  | Some(_) -> fprintf !err_fmt (yel ("[%a] " ^^ fmt ^^ "\n")) Pos.pp pos

(** [with_no_wrn f x] disables warnings before executing [f x] and then
    restores the initial state of warnings. The result of [f x] is returned.
 *)
let with_no_wrn : ('a -> 'b) -> 'a -> 'b = fun f x ->
  let open Stdlib in
  let w = !no_wrn in
  no_wrn := true;
  let res = f x in
  no_wrn := w;
  res

(** Exception raised in case of failure. Note that we use an optional optional
    source position. [None] is used on errors that are independant from source
    code position (e.g., errors related to command-line arguments parsing). In
    cases where positions are expected [Some None] may be used to indicate the
    abscence of a position. This may happen when terms are generated (e.g., by
    a form of desugaring). *)
exception Fatal of Pos.popt option * string

(** [fatal_str fmt] may be called an arbitrary number of times to build up the
    error message of the [fatal] or [fatal_no_pos] functions prior to  calling
    them. Note that the messages are stored in a buffer that is flushed by the
    [fatal] or [fatal_no_pos] function. Hence, they must be called. *)
let fatal_msg : 'a outfmt -> 'a =
  fun fmt -> Format.fprintf Format.str_formatter fmt

(** [fatal popt fmt] raises the [Fatal(popt,msg)] exception, in which [msg] is
    built from the format [fmt] (provided the necessary arguments. *)
let fatal : Pos.popt -> ('a,'b) koutfmt -> 'a = fun pos fmt ->
  let cont _ = raise (Fatal(Some(pos), Format.flush_str_formatter ())) in
  Format.kfprintf cont Format.str_formatter fmt

(** [fatal_no_pos fmt] is similar to [fatal _ fmt], but it is used to raise an
    error that has no precise attached source code position. *)
let fatal_no_pos : ('a,'b) koutfmt -> 'a = fun fmt ->
  let cont _ = raise (Fatal(None, Format.flush_str_formatter ())) in
  Format.kfprintf cont Format.str_formatter fmt

(** [handle_exceptions f] runs [f ()] in an exception handler and handles both
    expected and unexpected exceptions by displaying a graceful error message.
    In case of an error, the program is (irrecoverably) stopped with exit code
    [1] (indicating failure). Hence, [handle_exceptions] should only be called
    by the main program logic, not by the internals. *)
let handle_exceptions : (unit -> unit) -> unit = fun f ->
  let exit_with : type a b. (a,b) koutfmt -> a = fun fmt ->
    Format.(kfprintf (fun _ -> exit 1) err_formatter (red (fmt ^^ "\n%!")))
  in
  try f () with
  | Fatal(None,    msg) -> exit_with "%s" msg
  | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.pp p msg
  | e                   -> exit_with "Uncaught [%s]." (Printexc.to_string e)

(** Type of a logging function. *)
type logger = { logger : 'a. 'a outfmt -> 'a }

(** Type of logging function data. *)
type logger_data =
  { logger_key     : char     (** Character used to unable the logger.      *)
  ; logger_name    : string   (** 4 character name used as prefix in logs.  *)
  ; logger_desc    : string   (** Description of the log displayed in help. *)
  ; logger_enabled : bool ref (** Is the log enabled? *) }

(** [log_enabled] is (automatically) set to true by {!val:set_debug} or
    functions of {!module:State} when some logging functions may print
    messages. Its main use is to guard logging operations to avoid performing
    unnecessary computations. *)
let log_enabled : bool ref = ref false

(** [loggers] constains the registered logging functions. *)
let loggers : logger_data list Stdlib.ref = Stdlib.ref []

(** [default_loggers] give the loggers enabled by default. *)
let default_loggers : string Stdlib.ref = Stdlib.ref ""

(** [log_summary ()] gives the keys and descriptions for logging options. *)
let log_summary : unit -> (char * string) list = fun () ->
  let fn data = (data.logger_key, data.logger_desc) in
  let compare (c1, _) (c2, _) = Char.compare c1 c2 in
  List.sort compare (List.map fn Stdlib.(!loggers))

(** [set_log value key] enables or disables the loggers corresponding to every
    character of [str] according to [value]. *)
let set_debug : bool -> string -> unit = fun value str ->
  let fn {logger_key; logger_enabled; _} =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn Stdlib.(!loggers);
  let is_enabled data = !(data.logger_enabled) in
  log_enabled := List.exists is_enabled Stdlib.(!loggers)

(** [set_default_debug str] declares the debug flags of [str] to be enabled by
    default. *)
let set_default_debug : string -> unit = fun str ->
  Stdlib.(default_loggers := str); set_debug true str

(** [new_logger key name desc] returns (and registers) a new logger. *)
let new_logger : char -> string -> string -> logger = fun key name desc ->
  (* Sanity checks. *)
  if String.length name <> 4 then
    invalid_arg "Console.new_logger: name must be 4 characters long";
  let check data =
    if key = data.logger_key then
      invalid_arg "Console.new_logger: already used key";
    if name = data.logger_name then
      invalid_arg "Console.new_logger: already used name"
  in
  List.iter check Stdlib.(!loggers);
  (* Logger registration. *)
  let enabled = ref false in
  let data =
    { logger_key = key ; logger_name = name
    ; logger_desc = desc ; logger_enabled = enabled }
  in
  let cmp_loggers l1 l2 = Char.compare l1.logger_key l2.logger_key in
  Stdlib.(loggers := List.sort cmp_loggers (data :: !loggers));
  (* Actual printing function. *)
  let logger fmt =
    let pp = Format.(if !enabled then fprintf else ifprintf) in
    pp Stdlib.(!err_fmt) ((cya "[%s] ") ^^ fmt ^^ "\n%!") name
  in
  {logger}

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
