(** Output and debugging utilities. *)

open Timed
open Extra

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [color] tells whether colors can be used in the output. *)
let color : bool Pervasives.ref = Pervasives.ref true

(** Format transformers (colors). *)
let colorize k fmt =
  if Pervasives.(!color) then
    "\027[" ^^ k ^^ "m" ^^ fmt ^^ "\027[0m%!"
  else fmt

let red fmt = colorize "31" fmt
let gre fmt = colorize "32" fmt
let yel fmt = colorize "33" fmt
let blu fmt = colorize "34" fmt
let mag fmt = colorize "35" fmt
let cya fmt = colorize "36" fmt

let space fmt = " " ^^ fmt

(** [r_or_g cond fmt] colors the format [fmt] in green if [cond] is [true] and
    in red otherwise. *)
let r_or_g cond = if cond then gre else red

(** [out_fmt] main output formatter. *)
let out_fmt = Pervasives.ref Format.std_formatter

(** [err_fmt] warning/error output formatter. *)
let err_fmt = Pervasives.ref Format.err_formatter

(** [wrn popt fmt] prints a yellow warning message with [Printf] format [fmt].
    Note that the output buffer is flushed by the function, and that output is
    prefixed with the position [popt] if given. A newline is automatically put
    at the end of the message as well. *)
let wrn : Pos.popt -> 'a outfmt -> 'a = fun pos fmt ->
  match pos with
  | None    -> Format.fprintf Pervasives.(!err_fmt) (yel (fmt ^^ "\n"))
  | Some(_) -> Format.fprintf Pervasives.(!err_fmt)
                 (yel ("[%a] " ^^ fmt ^^ "\n")) Pos.print pos

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

(** [exit_with fmt] is similar to [fatal_no_pos fmt], but the whole program is
    (irrecoverably) stopped with return code [1], indicating failure. *)
let exit_with : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (red (fmt ^^ "\n%!"))

(** Type of a logging function. *)
type logger = { logger : 'a. 'a outfmt -> 'a }

(** Type of logging function data. *)
type logger_data =
  { logger_key     : char     (** Character used to unable the logger.      *)
  ; logger_name    : string   (** 4 character name used as prefix in logs.  *)
  ; logger_desc    : string   (** Description of the log displayed in help. *)
  ; logger_enabled : bool ref (** Is the log enabled? *) }

(** [log_enabled] is set to true when logging functions may print messages. *)
let log_enabled : bool ref = ref false

(** [loggers] constains the registered logging functions. *)
let loggers : logger_data list Pervasives.ref = Pervasives.ref []

(** [default_loggers] give the loggers enabled by default. *)
let default_loggers : string Pervasives.ref = Pervasives.ref ""

(** [log_summary ()] returns descriptions for logging options. *)
let log_summary : unit -> string list = fun () ->
  let fn data =
    Format.sprintf "%c : debugging information for %s"
      data.logger_key data.logger_desc
  in
  List.sort String.compare (List.map fn Pervasives.(!loggers))

(** [set_log value key] enables or disables the loggers corresponding to every
    character of [str] according to [value]. *)
let set_debug : bool -> string -> unit = fun value str ->
  let fn {logger_key; logger_enabled; _} =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn Pervasives.(!loggers);
  let is_enabled data = !(data.logger_enabled) in
  log_enabled := List.exists is_enabled Pervasives.(!loggers)

(** [set_default_debug str] declares the debug flags of [str] to be enabled by
    default. *)
let set_default_debug : string -> unit = fun str ->
  Pervasives.(default_loggers := str); set_debug true str

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
  List.iter check Pervasives.(!loggers);
  (* Logger registration. *)
  let enabled = ref false in
  let data =
    { logger_key = key ; logger_name = name
    ; logger_desc = desc ; logger_enabled = enabled }
  in
  let cmp_loggers l1 l2 = Char.compare l1.logger_key l2.logger_key in
  Pervasives.(loggers := List.sort cmp_loggers (data :: !loggers));
  (* Actual printing function. *)
  let logger fmt =
    let pp = Format.(if !enabled then fprintf else ifprintf) in
    pp Pervasives.(!err_fmt) ((cya "[%s] ") ^^ fmt ^^ "\n%!") name
  in
  {logger}

(** Current verbosity level. *)
let verbose = ref 1

(** Default verbosity level (may be set with command line arguments). *)
let default_verbose = Pervasives.ref 1

(** [set_default_verbose i] sets the default verbosity level to [i]. *)
let set_default_verbose : int -> unit = fun i ->
  Pervasives.(default_verbose := i); verbose := i

(** [out lvl fmt] prints an output message using the format [fmt], but only if
    [lvl] is strictly greater than the current verbosity level.  Note that the
    output channel is automatically flushed,  and  the message is displayed in
    magenta (and not default terminal color) if logging modes are enabled. *)
let out : int -> 'a outfmt -> 'a = fun lvl fmt ->
  let fmt = if !log_enabled then mag fmt else fmt ^^ "%!" in
  if lvl > !verbose then Format.ifprintf Pervasives.(!out_fmt) fmt
  else Format.fprintf Pervasives.(!out_fmt) fmt

(** List of registered boolean flags, with their default values. *)
let boolean_flags : (bool * bool ref) StrMap.t Pervasives.ref =
  Pervasives.ref StrMap.empty

(** [register_flag id d] registers a new boolean flag named [id], with default
    value of [d]. Note the name should not have been used previously. *)
let register_flag : string -> bool -> bool ref = fun id default ->
  if StrMap.mem id Pervasives.(!boolean_flags) then
    invalid_arg "Console.register_flag: already registered";
  let r = ref default in
  Pervasives.(boolean_flags := StrMap.add id (default, r) !boolean_flags); r

(** [set_flag id b] sets the value of the flag named [id] to be [b], or raises
    [Not_found] if no flag with this name was registered. *)
let set_flag : string -> bool -> unit = fun id b ->
  snd (StrMap.find id Pervasives.(!boolean_flags)) := b

(** [reset_default ()] resets the verbosity level and the state of the loggers
    to their default value (configurable by the user with command line flags).
    The boolean flags are also reset to their default values. *)
let reset_default : unit -> unit = fun () ->
  (* Reset verbosity level. *)
  verbose := Pervasives.(!default_verbose);
  (* Reset debugging flags. *)
  log_enabled := false;
  let reset l =
    let v = String.contains Pervasives.(!default_loggers) l.logger_key in
    l.logger_enabled := v; if v then log_enabled := true;
  in
  List.iter reset Pervasives.(!loggers);
  (* Reset flags to their default values. *)
  let reset _ (default, r) = r := default in
  StrMap.iter reset Pervasives.(!boolean_flags)

(** Stack of saved state for verbosity, loggers and boolean flags. *)
let saved_state : (int * (char * bool) list * bool StrMap.t) list ref = ref []

(** [push_state ()] saves the current state of [verbose], the loggers, and the
    boolean flags, pushing it to the stack. *)
let push_state : unit -> unit = fun () ->
  let verbose = !verbose in
  let loggers =
    let fn l = (l.logger_key, !(l.logger_enabled)) in
    List.map fn Pervasives.(!loggers)
  in
  let flags : bool StrMap.t =
    let fn (_,r) = !r in
    StrMap.map fn Pervasives.(!boolean_flags)
  in
  saved_state := (verbose, loggers, flags) :: !saved_state

(** [pop_state ()] restores the setting saved with [push_stack], removing them
    from the top of the stack at the same time. *)
let pop_state : unit -> unit = fun () ->
  let (v,l,f) =
    match !saved_state with
    | []   -> failwith "[Console.pop_state] not well-bracketed."
    | e::s -> saved_state := s; e
  in
  (* Reset verbosity level. *)
  verbose := v;
  (* Reset debugging flags. *)
  log_enabled := false;
  let reset logger =
    let v = try List.assoc logger.logger_key l with Not_found -> false in
    logger.logger_enabled := v; if v then log_enabled := true;
  in
  List.iter reset Pervasives.(!loggers);
  (* Reset boolean flags. *)
  let reset k (_,r) =
    try r := StrMap.find k f
    with Not_found -> ()
  in
  StrMap.iter reset Pervasives.(!boolean_flags)
