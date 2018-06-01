(** Output and debugging utilities. *)

(* Format transformers (colors). *)
let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m%!"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

(** [r_or_g cond fmt] colors the format [fmt] in green if [cond] is [true] and
    in red otherwise. *)
let r_or_g cond = if cond then gre else red

(** [out_fmt] main output formatter. Used by the IDE server. *)
let out_fmt = ref Format.std_formatter

(** [err_fmt] formatter where to output warnings and errors. Used by
    the IDE server to redirect the output. *)
let err_fmt = ref Format.err_formatter

(** [wrn fmt] prints a yellow warning message with [Printf] format [fmt]. Note
    that the output buffer is flushed by the function. *)
let wrn : ('a, Format.formatter, unit) format -> 'a =
  fun fmt -> Format.fprintf !err_fmt (yel fmt)

(** [err fmt] prints a red error message with [Printf] format [fmt]. Note that
    the output buffer is flushed by the function. *)
let err : ('a, Format.formatter, unit) format -> 'a =
  fun fmt -> Format.fprintf !err_fmt (red fmt)

(** Exception raised in case of failure. *)
exception Fatal of string

(** [fatal fmt] is like [err fmt], but it raises [Fatal]. *)
let fatal : ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a =
  fun fmt ->
    let cont _ = raise (Fatal(Format.flush_str_formatter ())) in
    Format.kfprintf cont Format.str_formatter fmt

(** [abort fmt] is similar to [fatal fmt], but it calls [exit 1], which cannot
    be catched in any way (the program just terminates with an error. *)
let abort : ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a =
  fun fmt ->
    Format.kfprintf (fun _ -> exit 1) Format.err_formatter (red fmt)

(* Various debugging / message flags. *)
let verbose    = ref 1
let debug      = ref false
let debug_eval = ref false
let debug_matc = ref false
let debug_unif = ref false
let debug_subj = ref false
let debug_type = ref false
let debug_equa = ref false
let debug_pars = ref false

(** [debug_enabled ()] indicates whether any debugging flag is enabled. *)
let debug_enabled : unit -> bool = fun () ->
  !debug || !debug_eval || !debug_unif || !debug_subj || !debug_matc ||
  !debug_type || !debug_equa || !debug_pars

(** [set_debug value str] sets the debugging flags corresponding to characters
    of [str] to [value]. *)
let set_debug : bool -> string -> unit = fun value ->
  let enable c =
    match c with
    | 'a' -> debug      := value
    | 'r' -> debug_eval := value
    | 'u' -> debug_unif := value
    | 'm' -> debug_matc := value
    | 's' -> debug_subj := value
    | 't' -> debug_type := value
    | 'e' -> debug_equa := value
    | 'p' -> debug_pars := value
    | _   -> wrn "Unknown debug flag %C\n" c
  in
  String.iter enable

(** [log name fmt] prints a message in the log with the [Printf] format [fmt].
    The message is identified with the name (or flag) [name],  and coloured in
    cyan. Note that the output buffer is flushed by the  function,  and that a
    newline character ['\n'] is appended to the output. *)
let log : string -> ('a, Format.formatter, unit) format -> 'a =
  fun name fmt -> Format.fprintf !err_fmt ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

(** [out lvl fmt] prints an output message with the [Printf] format [fmt] when
    [lvl] is strictly greater than the verbosity level.  The output channel is
    flushed by the function,  and the message is displayed in magenta (instead
    of the default terminal color) whenever a debugging mode is enabled. *)
let out : int -> ('a, Format.formatter, unit) format -> 'a = fun lvl fmt ->
  let fmt = if debug_enabled () then mag fmt else fmt ^^ "%!" in
  if lvl > !verbose then Format.ifprintf !out_fmt fmt
  else Format.fprintf !out_fmt fmt
