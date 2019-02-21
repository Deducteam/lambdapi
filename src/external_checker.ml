(** Call to external checkers.

    This module allows to call an external checker, used for confluence and
    termination checking. *)

open Extra
open Timed
open Console

(** [check cmd sign translator logging property] runs the checker specified
    by command [cmd] on the rewrite system of signature [sign] tranlated by
    [translator]. The return value is [Some true] in the case where the system
    is accepted by [cmd]. It is [Some false] if the system is refused by
    [cmd], and it is [None] if the tool cannot conclude.  Note that it is
    assumed that [cmd] corresponds to a command that outputs either ["YES"],
    ["NO"] or ["MAYBE"] as the first line of its standard output. The
    exception [Fatal] may be raised if [cmd] does not behave as expected.
    [checked_property] is for printing purpose *)
let check : string -> Sign.t -> (Format.formatter -> Sign.t -> unit) ->
            logger -> string -> bool option =
  fun cmd sign translator logging property ->
  (* Run the command. *)
  if !log_enabled then logging.logger "Running command [%s]" cmd;
  let (ic, oc, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  (* Feed it the XTC problem. *)
  translator (Format.formatter_of_out_channel oc) sign;
  flush oc; close_out oc;
  if !log_enabled then logging.logger "Wrote the data and closed the pipe.";
  (* Read the answer (and possible error messages). *)
  let out = input_lines ic in
  if !log_enabled && out <> [] then
    begin
      logging.logger "==== Data written to [stdout] ====";
      List.iter (logging.logger "%s") out;
      logging.logger "==================================";
    end;
  let err = input_lines ec in
  if !log_enabled && err <> [] then
    begin
      logging.logger "==== Data written to [stderr] ====";
      List.iter (logging.logger "%s") err;
      logging.logger "=================================="
    end;
  (* Terminate the process. *)
  match (Unix.close_process_full (ic, oc, ec), out) with
  | (Unix.WEXITED 0  , "YES"  ::_) -> Some true
  | (Unix.WEXITED 0  , "NO"   ::_) -> Some false
  | (Unix.WEXITED 0  , "MAYBE"::_) -> None
  | (Unix.WEXITED 0  , []        ) ->
     fatal_no_pos "The %s checker produced no output." property
  | (Unix.WEXITED 0  , a ::_       ) ->
     fatal_no_pos "The %s checker gave an unexpected answer: %s" property a
  | (Unix.WEXITED i  , _         ) ->
     fatal_no_pos "The %s checker returned with code [%i]." property i
  | (Unix.WSIGNALED i, _         ) ->
     fatal_no_pos "The %s checker was killed by signal [%i]." property i
  | (Unix.WSTOPPED  i, _         ) ->
     fatal_no_pos "The %s checker was stopped by signal [%i]." property i
