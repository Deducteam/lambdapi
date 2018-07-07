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

(* Various debugging / message flags. *)
let verbose    = ref 1
let debug      = ref false
let debug_eval = ref false
let debug_matc = ref false
let debug_solv = ref false
let debug_subj = ref false
let debug_type = ref false
let debug_equa = ref false
let debug_pars = ref false
let debug_meta = ref false
let debug_tac  = ref false

(** [debug_enabled ()] indicates whether any debugging flag is enabled. *)
let debug_enabled : unit -> bool = fun () ->
  !debug || !debug_eval || !debug_solv || !debug_subj || !debug_matc ||
  !debug_type || !debug_equa || !debug_pars || !debug_tac

(** [set_debug value str] sets the debugging flags corresponding to characters
    of [str] to [value]. *)
let set_debug : bool -> string -> unit = fun value ->
  let enable c =
    match c with
    | 'a' -> debug      := value
    | 'r' -> debug_eval := value
    | 'u' -> debug_solv := value
    | 'm' -> debug_matc := value
    | 's' -> debug_subj := value
    | 't' -> debug_type := value
    | 'e' -> debug_equa := value
    | 'p' -> debug_pars := value
    | 'c' -> debug_meta := value
    | 'i' -> debug_tac  := value
    | _   -> wrn "Unknown debug flag %C\n" c
  in
  String.iter enable

(** [log tag fmt] logs a message using the format [fmt]. Note that the message
    is identified by a [tag], which should (ideally) be a 4-character [string]
    for better formatting. Note that the output buffer is flushed,  and that a
    newline character ['\n'] is also automatically appended to the output. *)
let log : string -> 'a outfmt -> 'a = fun name fmt ->
  Format.fprintf Pervasives.(!err_fmt) ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

(** [out lvl fmt] prints an output message using the format [fmt], but only if
    [lvl] is strictly greater than the current verbosity level.  Note that the
    output channel is automatically flushed,  and the message is displayed in
    magenta instead of the default terminal color whenever a debugging mode is
    enabled. *)
let out : int -> 'a outfmt -> 'a = fun lvl fmt ->
  let fmt = if debug_enabled () then mag fmt else fmt ^^ "%!" in
  if lvl > !verbose then Format.ifprintf Pervasives.(!out_fmt) fmt
  else Format.fprintf Pervasives.(!out_fmt) fmt
