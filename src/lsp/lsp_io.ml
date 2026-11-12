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
let read_error msg = raise (ReadError msg)

let is_ows = function ' ' | '\t' -> true | _ -> false
let is_digit = function '0' .. '9' -> true | _ -> false

(* Trim only SP and HTAB (OWS): String.trim would also accept control
   characters that are invalid around the length. *)
let trim_ows s =
  let rec skip_start i =
    if i < String.length s && is_ows s.[i] then skip_start (i + 1) else i
  in
  let rec skip_end j start =
    if j > start && is_ows s.[j - 1] then skip_end (j - 1) start else j
  in
  let start = skip_start 0 in
  String.sub s start (skip_end (String.length s) start - start)

let parse_content_length value =
  let value = trim_ows value in
  if value = "" then read_error "empty Content-Length header"
  (* Checking the entire value rejects suffixes such as "12junk" and signs;
     int_of_string_opt then detects integer overflow. *)
  else if not (String.for_all is_digit value) then
    read_error "invalid Content-Length header"
  else
    match int_of_string_opt value with
    | Some size -> size
    | None -> read_error "Content-Length is too large"

let content_length_header = "content-length"

(* Header names are case-insensitive. Checking the length first avoids
   allocating a substring for every header that is not Content-Length. *)
let is_content_length line colon =
  colon = String.length content_length_header
  && String.equal
       (String.lowercase_ascii (String.sub line 0 colon))
       content_length_header

(* Return the end position of [line], excluding a possible trailing CR. *)
let content_end line =
  let len = String.length line in
  if len > 0 && line.[len - 1] = '\r' then len - 1 else len

let read_request ic =
  (* Read all headers so Content-Length can appear in any position, while
     rejecting ambiguous duplicates. *)
  let rec read_headers content_length =
    match input_line ic with
    | "" | "\r" -> content_length
    | line -> (
      match String.index_opt line ':' with
      | Some colon when is_content_length line colon ->
        if Option.is_some content_length then
          read_error "duplicate Content-Length header";
        let start = colon + 1 in
        let value = String.sub line start (content_end line - start) in
        read_headers (Some (parse_content_length value))
      | _ -> read_headers content_length)
  in
  try
    match read_headers None with
    | None -> read_error "missing Content-Length header"
    (* Reading exactly the announced size preserves message framing; invalid
       JSON is converted to ReadError below. *)
    | Some size -> J.from_string (really_input_string ic size)
  with
  | End_of_file -> read_error "EOF"
  | Yojson.Json_error msg -> read_error ("invalid JSON: " ^ msg)
  | Failure msg | Invalid_argument msg -> read_error msg

let send_json fmt obj =
  log_object "send" obj;
  let msg  = F.asprintf "%a" J.(pretty_print ~std:true) obj in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg

let notify_failure error_msg =
  let j = Lsp_base.mk_showMessage error_msg in
  (* send notification to user and log it in the log file *)
  send_json Format.std_formatter j;
  (* send log to client (will be visible in protocle output logs) *)
  Printf.eprintf "%s\n%!" error_msg
