(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant                            *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization Toplevel                                     *)
(* Copyright 2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

module F = Format
module J = Yojson.Basic

let debug_fmt = ref F.err_formatter

let log_error hdr msg =
  F.fprintf !debug_fmt "[%s]: @[%s@]@\n%!" hdr msg

let log_object hdr obj =
  F.fprintf !debug_fmt "[%s]: @[%a@]@\n%!" hdr J.(pretty_print ~std:false) obj

exception ReadError of string

(* Unbuffered input over [Unix.stdin], with our own line/exact-byte
   buffer. We can't use [Stdlib.in_channel] for stdin: it reads ahead
   of the current message into an opaque internal buffer, after which
   [Unix.select] on the file descriptor reports "no data ready" even
   though more messages are sitting in the OCaml buffer — breaking
   any peek-based debouncing. Owning the buffer ourselves lets us
   answer [bytes_pending ()] honestly. *)
let in_buf : Buffer.t = Buffer.create 4096

let drop_first n =
  let len = Buffer.length in_buf in
  if n >= len then Buffer.clear in_buf
  else begin
    let rest = Buffer.sub in_buf n (len - n) in
    Buffer.clear in_buf;
    Buffer.add_string in_buf rest
  end

let chunk = Bytes.create 4096

let read_more () =
  let n = Unix.read Unix.stdin chunk 0 (Bytes.length chunk) in
  if n = 0 then raise End_of_file;
  Buffer.add_subbytes in_buf chunk 0 n

(* Read up to and including the next ['\n']; return the line *without*
   the trailing ['\n'] (a trailing ['\r'] is preserved). *)
let rec read_line_ub () : string =
  let s = Buffer.contents in_buf in
  match String.index_opt s '\n' with
  | Some i ->
    let line = String.sub s 0 i in
    drop_first (i + 1);
    line
  | None ->
    read_more (); read_line_ub ()

let rec read_exact n : string =
  if Buffer.length in_buf >= n then begin
    let s = Buffer.sub in_buf 0 n in
    drop_first n;
    s
  end else begin
    read_more (); read_exact n
  end

(* True iff there are bytes already in our buffer or ready on the fd
   within [timeout] seconds. The buffer-first check is what makes the
   coalesce-pending-didChange path actually fire on tight bursts. *)
let bytes_pending ?(timeout = 0.0) () : bool =
  if Buffer.length in_buf > 0 then true
  else
    try
      let r, _, _ = Unix.select [Unix.stdin] [] [] timeout in
      r <> []
    with _ -> false

let read_request () : J.t =
  try
    let header = read_line_ub () in
    let size =
      Scanf.sscanf header "Content-Length: %d" (fun n -> n) in
    (* Consume the empty separator line (its '\n' was the second of
       a "\r\n\r\n" pair). *)
    let _ = read_line_ub () in
    J.from_string (read_exact size)
  with
  | End_of_file ->
    raise (ReadError "EOF")
  | Scanf.Scan_failure msg
  | Failure msg
  | Invalid_argument msg ->
    raise (ReadError msg)

let send_json fmt obj =
  log_object "send" obj;
  let msg  = F.asprintf "%a" J.(pretty_print ~std:true) obj in
  let size = String.length msg         in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg
