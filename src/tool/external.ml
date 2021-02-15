(** Call to external checkers.

    This module provides a high-level primitive to run an external checker, by
    calling a Unix command. This is used, for instance, to run a confluence or
    termination checker. *)

open Lplib.Base
open Lplib.Extra

open Common
open Error
open Timed
open Core
open Debug

(** Logging function for external checkers. *)
let log_xtrn = new_logger 'x' "xtrn" "external tools"
let log_xtrn = log_xtrn.logger

(** [run prop pp cmd sign] runs the external checker given by the Unix command
    [cmd] on the signature [sign]. The signature is processed and written to a
    Unix pipe using the formatter [pp],  and the produced output is fed to the
    command on its standard output. The return value is [Some true] in case of
    a successful check, [Some false] in the case of a failed check, and [None]
    if the external tool cannot conclude.  Note  that the command [cmd] should
    write either ["YES"], ["NO"] or ["MAYBE"] as its first line of  (standard)
    output.  The exception [Fatal] may be raised if [cmd] exhibits a different
    behavior. The name [prop] is used to refer to the checked property when an
    error message is displayed. *)
let run : string -> Sign.t pp -> string -> Sign.t -> bool option =
    fun prop pp cmd sign ->
  (* Run the command. *)
  if !log_enabled then log_xtrn "Running %s command [%s]" prop cmd;
  let (ic, oc, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  (* Feed it the printed signature. *)
  pp (Format.formatter_of_out_channel oc) sign;
  flush oc; close_out oc;
  if !log_enabled then log_xtrn "Wrote the data and closed the pipe.";
  (* Read the answer (and possible error messages). *)
  let out = input_lines ic in
  if !log_enabled && out <> [] then
    begin
      log_xtrn "==== Data written to [stdout] ====";
      List.iter (log_xtrn "%s") out;
      log_xtrn "==================================";
    end;
  let err = input_lines ec in
  if !log_enabled && err <> [] then
    begin
      log_xtrn "==== Data written to [stderr] ====";
      List.iter (log_xtrn "%s") err;
      log_xtrn "=================================="
    end;
  (* Terminate the process. *)
  match (Unix.close_process_full (ic, oc, ec), out) with
  | (Unix.WEXITED 0  , "YES"  ::_) -> Some true
  | (Unix.WEXITED 0  , "NO"   ::_) -> Some false
  | (Unix.WEXITED 0  , "MAYBE"::_) -> None
  | (Unix.WEXITED 0  , []        ) ->
      fatal_no_pos "The %s checker produced no output." prop
  | (Unix.WEXITED 0  , a ::_       ) ->
      fatal_no_pos "The %s checker gave an unexpected answer: %s" prop a
  | (Unix.WEXITED i  , _         ) ->
      fatal_no_pos "The %s checker returned with code [%i]." prop i
  | (Unix.WSIGNALED i, _         ) ->
      fatal_no_pos "The %s checker was killed by signal [%i]." prop i
  | (Unix.WSTOPPED  i, _         ) ->
      fatal_no_pos "The %s checker was stopped by signal [%i]." prop i

(** {b NOTE} that for any given property being checked,  the simplest possible
    valid command is ["echo MAYBE"]. Moreover,  ["cat > file; echo MAYBE"] can
    conveniently be used to write generated data to the file ["file"]. This is
    useful for debugging purposes. *)
