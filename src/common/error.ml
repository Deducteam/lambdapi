(** Warnings and errors. *)

open Lplib open Base

(** [err_fmt] warning/error output formatter. *)
let err_fmt = Stdlib.ref Format.err_formatter

(** [no_wrn] disables warnings when set to [true]. *)
let no_wrn = Stdlib.ref false

(** [wrn popt fmt] prints a yellow warning message with [Format] format [fmt].
    Note that the output buffer is flushed by the function, and that output is
    prefixed with the position [popt] if given. A newline is automatically put
    at the end of the message as well. *)
let wrn : Pos.popt -> 'a outfmt -> 'a = fun pos fmt ->
  Color.update_with_color !err_fmt;
  let open Stdlib in
  let fprintf = if !no_wrn then Format.ifprintf else out in
  match pos with
  | None   -> fprintf !err_fmt (Color.yel fmt ^^ "@.")
  | Some _ ->
    fprintf !err_fmt (Color.yel ("[%a]@ " ^^ fmt ^^ "@.")) Pos.pp pos

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
  fun fmt -> out Format.str_formatter fmt

(** [fatal popt fmt] raises the [Fatal(popt,msg)] exception, in which [msg] is
    built from the format [fmt] (provided the necessary arguments). *)
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
  Color.update_with_color Format.err_formatter;
  let exit_with : type a b. (a,b) koutfmt -> a = fun fmt ->
    Format.kfprintf (fun _ -> exit 1) Format.err_formatter
      (Color.red (fmt ^^ "@."))
  in
  try f () with
  | Fatal(None,    msg) -> exit_with "%s" msg
  | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.pp p msg
  | e                   -> exit_with "Uncaught [%s]." (Printexc.to_string e)
