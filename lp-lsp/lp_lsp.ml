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
module U = Yojson.Basic.Util

let    int_field name dict = U.to_int    List.(assoc name dict)
let   dict_field name dict = U.to_assoc  List.(assoc name dict)
let   list_field name dict = U.to_list   List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

(* Conditionals *)
let option_cata f x d = match x with | None -> d | Some x -> f x
let option_default x d = match x with | None -> d | Some x -> x

let oint_field  name dict = option_cata U.to_int List.(assoc_opt name dict) 0
let odict_field name dict = option_default U.(to_option to_assoc (option_default List.(assoc_opt name dict) `Null)) []

module LIO = Lsp_io
module LSP = Lsp_base

(* Request Handling: The client expects a reply *)
let do_initialize ofmt ~id _params =
  let msg = LSP.mk_reply ~id ["capabilities", `Assoc ["textDocumentSync", `Int 1]] in
  LIO.send_json ofmt msg

let do_shutdown ofmt ~id =
  let msg = LSP.mk_reply ~id [] in
  LIO.send_json ofmt msg

(* Notificatio handling; reply is optional / asynchronous *)
let do_check_text ofmt ~doc file version text =
  LIO.send_json ofmt @@ Lp_doc.check_text ~doc file version text

let do_change ofmt ~doc file version change =
  LIO.log_error "checking file" (file ^ " / version: " ^ (string_of_int version));
  let text = string_field "text" change in
  do_check_text ofmt ~doc file version text

let doc_table : (string, Pure.state) Hashtbl.t = Hashtbl.create 39

let do_open ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file, doc_ver, doc_text =
    LSP.parse_uri @@ string_field "uri" document,
    int_field "version" document,
    string_field "text" document in
  let doc = Lp_doc.new_doc [doc_file] in
  begin match Hashtbl.find_opt doc_table doc_file with
    | None -> ()
    | Some _ -> LIO.log_error "do_open" ("file " ^ doc_file ^ " not properly closed by client")
  end;
  Hashtbl.add doc_table doc_file doc;
  do_check_text ofmt ~doc doc_file doc_ver doc_text

let do_change ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file, doc_ver  = LSP.parse_uri @@ string_field "uri" document, int_field "version" document in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  let doc = Hashtbl.find doc_table doc_file in
  List.iter (do_change ofmt ~doc doc_file doc_ver) changes

let do_close _ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file = LSP.parse_uri @@ string_field "uri" document in
  Hashtbl.remove doc_table doc_file

(* XXX: We could split requests and notifications but with the OCaml
   theading model there is not a lot of difference yet; something to
   think for the future. *)
let dispatch_message ofmt dict =
  let id     = oint_field "id" dict in
  let params = odict_field "params" dict in
  match string_field "method" dict with
  (* Requests *)
  | "initialize" ->
    do_initialize ofmt ~id params
  | "shutdown" ->
    do_shutdown ofmt ~id

  (* Notifications *)
  | "textDocument/didOpen" ->
    do_open ofmt params
  | "textDocument/didChange" ->
    do_change ofmt params
  | "textDocument/didClose" ->
    do_close ofmt params
  | "exit" ->
    exit 0

  (* NOOPs *)
  | "initialized"
  | "workspace/didChangeWatchedFiles" ->
    ()
  | msg ->
    LIO.log_error "no_handler" msg

let process_input ofmt (com : J.json) =
  try dispatch_message ofmt (U.to_assoc com)
  with
  | U.Type_error (msg, obj) ->
    LIO.log_object msg obj
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[BT]" bt;
    LIO.log_error "process_input" (Printexc.to_string exn)

let my_main () =

  Printexc.record_backtrace true;

  let oc = F.std_formatter in

  let debug_oc = open_out "log-lsp.txt" in
  LIO.debug_fmt := F.formatter_of_out_channel debug_oc;

  (* XXX: Capture better / per sentence. *)
  let lp_oc = open_out "log-lp.txt" in
  let lp_fmt = F.formatter_of_out_channel lp_oc in
  Console.out_fmt := lp_fmt;
  Console.err_fmt := lp_fmt;
  (* Console.verbose := 4; *)

  let rec loop () =
    let com = LIO.read_request stdin in
    LIO.log_object "read" com;
    process_input oc com;
    F.pp_print_flush lp_fmt (); flush lp_oc;
    loop ()
  in
  try loop ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[fatal error]" Printexc.(to_string exn);
    LIO.log_error "[BT]" bt;
    F.pp_print_flush !LIO.debug_fmt ();
    flush_all ();
    close_out debug_oc;
    close_out lp_oc

let _ = my_main ()
