(** Output and debugging utilities. *)

open Timed

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** Format transformers (colors). *)
let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m%!"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

(** [r_or_g cond fmt] colors the format [fmt] in green if [cond] is [true] and
    in red otherwise. *)
let r_or_g cond = if cond then gre else red

(** [out_fmt] main output formatter. *)
let out_fmt = Pervasives.ref Format.std_formatter

(** [err_fmt] warning/error output formatter. *)
let err_fmt = Pervasives.ref Format.err_formatter

(** [wrn fmt] prints a yellow warning message with [Printf] format [fmt]. Note
    that the output buffer is flushed by the function. *)
let wrn : 'a outfmt -> 'a = fun fmt ->
  Format.fprintf Pervasives.(!err_fmt) (yel fmt)

(** Exception raised in case of failure. *)
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

(** [fatal_no_pos fmt] is equivalent to [fatal None fmt]. *)
let fatal_no_pos : ('a,'b) koutfmt -> 'a = fun fmt -> fatal None fmt

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

(** [log_summary ()] returns descriptions for logging options. *)
let log_summary : unit -> string list = fun () ->
  let fn data = Format.sprintf "%c : %s" data.logger_key data.logger_desc in
  List.sort String.compare (List.map fn Pervasives.(!loggers))

(** [set_log value key] enables or disables the loggers corresponding to every
    character of [str] according to [value]. *)
let set_debug : bool -> string -> unit = fun value str ->
  let fn {logger_key; logger_enabled} =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn Pervasives.(!loggers);
  let is_enabled data = !(data.logger_enabled) in
  log_enabled := List.exists is_enabled Pervasives.(!loggers)

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

(* Current verbosity level. *)
let verbose    = ref 1

(** [out lvl fmt] prints an output message using the format [fmt], but only if
    [lvl] is strictly greater than the current verbosity level.  Note that the
    output channel is automatically flushed,  and  the message is displayed in
    magenta (and not default terminal color) if logging modes are enabled. *)
let out : int -> 'a outfmt -> 'a = fun lvl fmt ->
  let fmt = if !log_enabled then mag fmt else fmt ^^ "%!" in
  if lvl > !verbose then Format.ifprintf Pervasives.(!out_fmt) fmt
  else Format.fprintf Pervasives.(!out_fmt) fmt
