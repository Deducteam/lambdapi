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

let read_request ic =
  try
    (* Read header lines up to the empty "\r\n" separator, taking the
       size from whichever one is [Content-Length] (a client may also
       send e.g. [Content-Type], in any order). [input_line] strips
       the '\n'; a trailing '\r' remains. *)
    let rec content_length acc =
      match input_line ic with
      | "" | "\r" -> acc
      | line ->
        let acc =
          try Scanf.sscanf line "Content-Length: %d" (fun n -> Some n)
          with Scanf.Scan_failure _ | Failure _ -> acc
        in
        content_length acc
    in
    match content_length None with
    | None -> raise (ReadError "missing Content-Length header")
    | Some size ->
      let buf = Bytes.create size in
      really_input ic buf 0 size;
      J.from_string (Bytes.to_string buf)
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
