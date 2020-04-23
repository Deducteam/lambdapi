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
  let cl = input_line ic in
  let sin = Scanf.Scanning.from_string cl in
  try
    let raw_obj =
      Scanf.bscanf sin "Content-Length: %d\r" (fun size ->
          let buf = Bytes.create size in
          (* Consume the second \r\n *)
          let _ = input_line ic in
          really_input ic buf 0 size;
          Bytes.to_string buf
        ) in
    J.from_string raw_obj
  with
  (* if the end of input is encountered while some more characters are needed
     to read the current conversion specification. *)
  | End_of_file ->
    raise (ReadError "EOF")
  (* if the input does not match the format. *)
  | Scanf.Scan_failure msg
  (* if a conversion to a number is not possible. *)
  | Failure msg
  (* if the format string is invalid. *)
  | Invalid_argument msg ->
    raise (ReadError msg)

let send_json fmt obj =
  log_object "send" obj;
  let msg  = F.asprintf "%a" J.(pretty_print ~std:true) obj in
  let size = String.length msg         in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg
