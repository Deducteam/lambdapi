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

(** [wrn fmt] prints a yellow warning message with [Printf] format [fmt]. Note
    that the output buffer is flushed by the function. *)
let wrn : ('a, out_channel, unit) format -> 'a =
  fun fmt -> Printf.eprintf (yel fmt)

(** [err fmt] prints a red error message with [Printf] format [fmt]. Note that
    the output buffer is flushed by the function. *)
let err : ('a, out_channel, unit) format -> 'a =
  fun fmt -> Printf.eprintf (red fmt)

(** [fatal fmt] is like [err fmt], but it aborts the program with [exit 1]. *)
let fatal : ('a, out_channel, unit, unit, unit, 'b) format6 -> 'a =
  fun fmt -> Printf.kfprintf (fun _ -> exit 1) stderr (red fmt)

(* Various debugging / message flags. *)
let verbose    = ref 1
let debug      = ref false
let debug_eval = ref false
let debug_infr = ref false
let debug_patt = ref false
let debug_type = ref false

(** [debug_enabled ()] indicates whether any debugging flag is enabled. *)
let debug_enabled : unit -> bool = fun () ->
  !debug || !debug_eval || !debug_infr || !debug_patt || !debug_type

(** [set_debug value str] sets the debugging flags corresponding to characters
    of [str] to [value]. *)
let set_debug : bool -> string -> unit = fun value ->
  let enable c =
    match c with
    | 'a' -> debug      := value
    | 'e' -> debug_eval := value
    | 'i' -> debug_infr := value
    | 'p' -> debug_patt := value
    | 't' -> debug_type := value
    | _   -> wrn "Unknown debug flag %C\n" c
  in
  String.iter enable

(** [log name fmt] prints a message in the log with the [Printf] format [fmt].
    The message is identified with the name (or flag) [name],  and coloured in
    cyan. Note that the output buffer is flushed by the  function,  and that a
    newline character ['\n'] is appended to the output. *)
let log : string -> ('a, out_channel, unit) format -> 'a =
  fun name fmt -> Printf.eprintf ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

(** [out lvl fmt] prints an output message with the [Printf] format [fmt] when
    [lvl] is strictly greater than the verbosity level.  The output channel is
    flushed by the function,  and the message is displayed in magenta (instead
    of the default terminal color) whenever a debugging mode is enabled. *)
let out : int -> ('a, out_channel, unit) format -> 'a = fun lvl fmt ->
  let fmt = if debug_enabled () then mag fmt else fmt ^^ "%!" in
  if lvl > !verbose then Printf.ifprintf stdout fmt else Printf.printf fmt
