(** Warnings and errors. *)

open Lplib open Base

(** [err_fmt] warning/error output formatter. *)
let err_fmt = Stdlib.ref Format.err_formatter

(** [no_warnings] disables warnings when set to [true]. *)
let no_warnings = Stdlib.ref false

(** [wrn popt fmt] prints a yellow warning message with [Format] format [fmt].
    Note that the output buffer is flushed by the function, and that output is
    prefixed with the position [popt] if given. A newline is automatically put
    at the end of the message as well. *)
let wrn : Pos.popt -> 'a outfmt -> 'a = fun pos fmt ->
  Color.update_with_color !err_fmt;
  let open Stdlib in
  let fprintf = if !no_warnings then Format.ifprintf else out in
  match pos with
  | None   -> fprintf !err_fmt (Color.yel fmt ^^ "@.")
  | Some _ ->
    fprintf !err_fmt (Color.yel ("[%a]@ " ^^ fmt) ^^ "@.") Pos.pp pos

(** [no_wrn f x] disables warnings before executing [f x] and then restores
    the initial state of warnings. The result of [f x] is returned. *)
let no_wrn : ('a -> 'b) -> 'a -> 'b = fun f x ->
  let open Stdlib in
  let w = !no_warnings in
  no_warnings := true;
  let res = f x in
  no_warnings := w;
  res

(** Exception raised in case of failure. Note that we use an optional optional
    source position. [None] is used on errors that are independant from source
    code position (e.g., errors related to command-line arguments parsing). In
    cases where positions are expected [Some None] may be used to indicate the
    abscence of a position. This may happen when terms are generated (e.g., by
    a  form of desugaring). The last argument is  used to provide  an optional
    description of the error, displayed differently from the error itself. *)
exception Fatal of Pos.popt option * string * string

(** [fatal_msg fmt] may be called an arbitrary number of times to build up the
    error message of the [fatal] or [fatal_no_pos] functions prior to  calling
    them. Note that the messages are stored in a buffer that is flushed by the
    [fatal] or [fatal_no_pos] function. Hence, they must be called. *)
let fatal_msg : 'a outfmt -> 'a =
  fun fmt -> out Format.str_formatter fmt

(** [fatal popt fmt] raises the [Fatal(popt,msg,err_desc)] exception, in which
    [msg] is built from the format [fmt] (provided the necessary arguments).
    [err_desc] continues the error message and is printed in normal format
    instead of red color. *)
let fatal : Pos.popt -> ?err_desc:string -> ('a,'b) koutfmt -> 'a =
  fun pos ?(err_desc="") fmt ->
  let err_desc _ =
    raise (Fatal(Some(pos), Format.flush_str_formatter (), err_desc)) in
  Format.kfprintf err_desc Format.str_formatter fmt

(** [fatal_no_pos fmt] is similar to [fatal _ fmt], but it is used to raise an
    error that has no precise attached source code position. *)
let fatal_no_pos : ?err_desc:string -> ('a,'b) koutfmt -> 'a =
  fun ?(err_desc="") fmt ->
    let cont _ =
      raise (Fatal(None, Format.flush_str_formatter (), err_desc)) in
    Format.kfprintf cont Format.str_formatter fmt

let fatal_optional_position = function
  | None -> fatal_no_pos
  | Some p -> fatal p
