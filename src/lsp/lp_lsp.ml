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

open! Lplib
open Lplib.Extra
open Common

open Core

module F = Format
module J = Yojson.Basic
module U = Yojson.Basic.Util

let    int_field name dict = U.to_int    List.(assoc name dict)
let   dict_field name dict = U.to_assoc  List.(assoc name dict)
let   list_field name dict = U.to_list   List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

(* Conditionals *)
let oint_field  name dict =
  Option.map_default U.to_int 0 List.(assoc_opt name dict)
let odict_field name dict =
  Option.default U.(to_option to_assoc
                      (Option.default List.(assoc_opt name dict) `Null)) []

module LIO = Lsp_io
module LSP = Lsp_base

(* Request Handling: The client expects a reply *)
let do_initialize ofmt ~id _params =
  let msg = LSP.mk_reply ~id ~result:(
      `Assoc ["capabilities",
       `Assoc [
          "textDocumentSync", `Int 1
        ; "documentSymbolProvider", `Bool true
        ; "hoverProvider", `Bool true
        ; "definitionProvider", `Bool true
        ; "codeActionProvider", `Bool false
        ]]) in
  LIO.send_json ofmt msg

let do_shutdown ofmt ~id =
  let msg = LSP.mk_reply ~id ~result:`Null in
  LIO.send_json ofmt msg

let doc_table : (string, _) Hashtbl.t = Hashtbl.create 39
let completed_table : (string, Lp_doc.t) Hashtbl.t = Hashtbl.create 39

(* Notification handling; reply is optional / asynchronous *)
let do_check_text ofmt ~doc =
  let doc, diags = Lp_doc.check_text ~doc in
  Hashtbl.replace doc_table doc.uri doc;
  Hashtbl.replace completed_table doc.uri doc;
  LIO.send_json ofmt @@ diags

let do_change ofmt ~doc change =
  let open Lp_doc in
  LIO.log_error "checking file"
    (doc.uri ^ " / version: " ^ (string_of_int doc.version));
  let doc = { doc with text = string_field "text" change; } in
  do_check_text ofmt ~doc

let do_open ofmt params =
  let document = dict_field "textDocument" params in
  let uri, version, text =
    string_field "uri" document,
    int_field "version" document,
    string_field "text" document in
  let doc = Lp_doc.new_doc ~uri ~text ~version in
  begin match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ ->
        LIO.log_error "do_open"
          ("file " ^ uri ^ " not properly closed by client")
  end;
  Hashtbl.add doc_table uri doc;
  do_check_text ofmt ~doc

let do_change ofmt params =
  let document = dict_field "textDocument" params in
  let uri, version  =
    string_field "uri" document,
    int_field "version" document in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  let doc = Hashtbl.find doc_table uri in
  let doc = { doc with Lp_doc.version; } in
  List.iter (do_change ofmt ~doc) changes

let do_close _ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in
  Hashtbl.remove doc_table doc_file

let grab_doc params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in

  let start_doc, end_doc =
    Hashtbl.(find doc_table doc_file, find completed_table doc_file) in
  doc_file, start_doc, end_doc

let mk_syminfo file (name, _path, kind, pos) : J.t =
  `Assoc [
    "name", `String name;
    "kind", `Int kind;            (* function *)
    "location", `Assoc [
                    "uri", `String file
                  ; "range", LSP.mk_range pos
                  ]
  ]

let mk_definfo file pos =
  `Assoc [
      "uri", `String file
    ; "range", LSP.mk_range pos
        ]

let kind_of_type tm =
  let open Term in
  let open Timed in
  let is_undef =
    Option.empty !(tm.sym_def) && List.length !(tm.sym_rules) = 0 in
  match !(tm.sym_type) with
  | Vari _ ->
    13                         (* Variable *)
  | Type | Kind | Symb _ | _ when is_undef ->
    14                         (* Constant *)
  | _ ->
    12                         (* Function *)

let do_symbols ofmt ~id params =
  let file, _, doc = grab_doc params in
  let sym = Pure.get_symbols doc.final in
  let sym =
    Extra.StrMap.fold
      (fun _ (s,p) l ->
        let open Term in
        (* LIO.log_error "sym"
         ( s.sym_name ^ " | "
         ^ Format.asprintf "%a" pp_term !(s.sym_type)); *)
        Option.map_default
          (fun p -> mk_syminfo file
              (s.sym_name, s.sym_mod, kind_of_type s, p) :: l) l p)
      sym [] in
  let msg = LSP.mk_reply ~id ~result:(`List sym) in
  LIO.send_json ofmt msg

let get_docTextPosition params =
  let document = dict_field "textDocument" params in
  let file = string_field "uri" document in
  let pos = dict_field "position" params in
  let line, character = int_field "line" pos, int_field "character" pos in
  file, line, character

let get_textPosition params =
  let pos = dict_field "position" params in
  let line, character = int_field "line" pos, int_field "character" pos in
  line, character

let in_range ?loc (line, pos) =
  match loc with
  | None -> false
  | Some Pos.{start_line; start_col; end_line; end_col; _} ->
    start_line - 1 < line && line < end_line - 1 ||
    (start_line - 1 = line && start_col <= pos) ||
    (end_line - 1 = line && pos <= end_col)

let get_node_at_pos doc line pos =
  let open Lp_doc in
  List.find_opt (fun { ast; _ } ->
      let loc = Pure.Command.get_pos ast in
      let res = in_range ?loc (line,pos) in
      let ls = Format.asprintf "%B l:%d p:%d / %a "
                 res line pos Pos.pp loc in
      LIO.log_error "get_node_at_pos" ("call: "^ls);
      res
    ) doc.Lp_doc.nodes

let rec get_goals ~doc ~line ~pos =
  let node = get_node_at_pos doc line pos in
  let goals = match node with
    | None -> None
    | Some n ->
        List.find_opt (fun (_, loc) -> in_range ?loc (line,pos)) n.goals in
  match goals with
    | None -> begin match node with
              | None   -> None
              | Some _ -> get_goals ~doc ~line:(line-1) ~pos:0 end
    | Some (v,_) -> Some v

let get_logs ~doc ~line ~pos =
  (* DEBUG LOG START *)
  LIO.log_error "get_logs"
    (Printf.sprintf "%s:%d,%d" doc.Lp_doc.uri line pos);
  let log_to_str (log, posopt) =
    let pos_str =
      match posopt with
      | None -> "None"
      | Some Pos.{start_line; start_col; _} ->
          Printf.sprintf "(%d, %d)" start_line start_col
    in
    let log_str =
      let len = String.length log in
      Printf.sprintf "length: %d | %s" len (String.sub log 0 (min 30 len))in
    Format.asprintf "element: %s -> %s\n " pos_str log_str
  in
  Lsp_io.log_error "get_logs"
    (List.fold_left (^) "\n" (List.map log_to_str doc.Lp_doc.logs));
  (* DEBUG LOG END *)
  let before_cursor (npos : Pos.popt) =
    match npos with
    | None -> Lsp_io.log_error "get_logs" "None pos"; true
    | Some Pos.{start_line; _} -> start_line-1 <= line
  in
  List.fold_left_while (fun acc x -> acc^(fst x))
                  (fun (_, p) -> before_cursor p) "" doc.Lp_doc.logs

let do_goals ofmt ~id params =
  let uri, line, pos = get_docTextPosition params in
  let doc = Hashtbl.find completed_table uri in
  let goals = get_goals ~doc ~line ~pos in
  let logs = get_logs ~doc ~line ~pos in
  let result = LSP.json_of_goals goals ~logs in
  let msg = LSP.mk_reply ~id ~result in
  LIO.send_json ofmt msg

let msg_fail hdr msg =
  LIO.log_error hdr msg;
  failwith msg

let get_symbol : Range.point ->
('a * 'b) RangeMap.t -> ('b * Range.t) option
= fun pos doc ->

  let open RangeMap in

  match (find pos doc) with
  | None -> None
  | Some(interval, (_, token)) -> Some (token, interval)


let do_definition ofmt ~id params =

  let _, _, doc = grab_doc params in
  let ln, pos = get_textPosition params in

  (* Lines send by the client start at 0 *)
  let pt = Range.make_point (ln + 1) pos in
  let sym_target =
    match get_symbol pt doc.map with
    | None -> "No symbol found"
    | Some(token, _) -> token
  in

  (*Some printing in the log*)
  LIO.log_error "token map" (RangeMap.to_string snd doc.map);
  LIO.log_error "do_definition" sym_target;

  let sym = Pure.get_symbols doc.final in
  let map_pp : string =
    Extra.StrMap.bindings sym
    |> List.map (fun (key, (sym,pos)) ->
        Format.asprintf "{%s} / %s: @[%a@]"
          key sym.Term.sym_name Pos.pp pos)
    |> String.concat "\n"
  in
  LIO.log_error "symbol map" map_pp;

  let sym_info =
    match StrMap.find_opt sym_target sym with
    | None
    | Some (_, None) -> `Null
    | Some (term, Some pos) ->
      (* A JSON with the path towards the definition of the term
         and its position is returned
         /!\ : extension is fixed, only works for .lp files *)
      mk_definfo Module.(file_of_mod Term.(term.sym_mod)
      ^ src_extension) pos
  in
  let msg = LSP.mk_reply ~id ~result:sym_info in
  LIO.send_json ofmt msg

let hover_symInfo ofmt ~id params =

  let _, _, doc = grab_doc params in
  let ln, pos = get_textPosition params in

  (* Positions sent by the client are one line late *)
  let pt = Range.make_point (ln + 1) pos in
  LIO.log_error "searched point" (Range.point_to_string pt);

  (* The hovered token and its start/finish positions are stored *)
  let sym_target, interval  =
  match get_symbol pt doc.map with
    | None ->
      "No symbol found", (Range.make_interval pt pt)
    (* VSCode highlights the token properly if the interval is extended to the
       character next to it. This might be handled differently in other
       editors in the future, but it is the most practical solution for
       now. *)
    | Some(token, range) ->
      token, (Range.translate range 0 1)
  in

  (* Some printing in the log *)
  (* LIO.log_error "token map" (RangeMap.to_string snd doc.map);

  LIO.log_error "hoverSymInfo" sym_target;
  LIO.log_error "hoverSymInfo" (Range.interval_to_string interval); *)

  (* The information about the tokens is stored *)
  let sym = Pure.get_symbols doc.final in

  (* The start/finish positions are used to hover the full qualified term,
     not just the token *)
  let start = Range.interval_start interval
  and finish = Range.interval_end interval in

  (* FIXME: types and typed conversion should take care of this *)
  let sl, sc, fl, fc =
    (Range.line start - 1),
    (Range.column start - 1),
    (Range.line finish - 1),
    (Range.column finish - 1)
  in

  let s = `Assoc["line", `Int sl; "character", `Int sc] in
  let f = `Assoc["line", `Int fl; "character", `Int fc] in
  let range = `Assoc["start", s; "end", f] in

  let map_pp : string =
    Extra.StrMap.bindings sym
    |> List.map (fun (key, (sym,pos)) ->
        Format.asprintf "{%s} / %s: @[%a@]"
          key sym.Term.sym_name Pos.pp pos)
    |> String.concat "\n"
  in
  LIO.log_error "symbol map" map_pp;

  try
    let sym_found =
      let open Timed in
      let open Term in
      match StrMap.find_opt sym_target sym with
      | None
      | Some (_, None) ->
        msg_fail "hover_SymInfo" "Sym not found"
      | Some (sym, Some _) ->
        !(sym.sym_type)
    in
    let sym_type = Format.asprintf "%a" Print.pp_term sym_found in
    let result : J.t =
      `Assoc [ "contents", `String sym_type; "range", range ] in
    let msg = LSP.mk_reply ~id ~result in
    LIO.send_json ofmt msg

  with _ ->
    let msg = LSP.mk_reply ~id ~result:`Null in
    LIO.send_json ofmt msg

let protect_dispatch p f x =
  try f x
  with
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error ("[error] {"^p^"}") Printexc.(to_string exn);
    LIO.log_error "[BT]" bt;
    F.pp_print_flush !LIO.debug_fmt ()

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

  (* Symbols in the document *)
  | "textDocument/documentSymbol" ->
    (* XXX to investigate *)
    protect_dispatch "do_symbols"
      (do_symbols ofmt ~id) params

  | "textDocument/hover" ->
    hover_symInfo ofmt ~id params

  | "textDocument/definition" ->
    do_definition ofmt ~id params

  | "proof/goals" ->
    do_goals ofmt ~id params

  (* Notifications *)
  | "textDocument/didOpen" ->
    protect_dispatch "didOpen"
      (do_open ofmt) params

  | "textDocument/didChange" ->
    protect_dispatch "didChange"
      (do_change ofmt) params

  | "textDocument/didClose" ->
    protect_dispatch "didClose"
      (do_close ofmt) params

  | "exit" ->
    exit 0

  (* NOOPs *)
  | "initialized"
  | "workspace/didChangeWatchedModule" ->
    ()
  | msg ->
    LIO.log_error "no_handler" msg

let process_input ofmt (com : J.t) =
  try dispatch_message ofmt (U.to_assoc com)
  with
  | U.Type_error (msg, obj) ->
    LIO.log_object msg obj
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[BT]" bt;
    LIO.log_error "process_input" (Printexc.to_string exn)

let main std log_file =

  Printexc.record_backtrace true;
  LSP.std_protocol := std;

  let oc = F.std_formatter in

  let debug_oc = open_out_gen [Open_append;Open_creat] 511 log_file in
  LIO.debug_fmt := F.formatter_of_out_channel debug_oc;

  (* XXX: Capture better / per sentence. *)
  (* let lp_oc = open_out "log-lp.txt" in *)
  let lp_fmt = F.formatter_of_buffer Lp_doc.lp_logger in
  Console.out_fmt := lp_fmt;
  Console.err_fmt := lp_fmt;
  (* Console.verbose := 4; *)

  let rec loop () =
    let com = LIO.read_request stdin in
    LIO.log_object "read" com;
    process_input oc com;
    F.pp_print_flush lp_fmt ();
    (* flush lp_oc ;*)
    loop ()
  in
  try loop ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[fatal error]" Printexc.(to_string exn);
    LIO.log_error "[BT]" bt;
    F.pp_print_flush !LIO.debug_fmt ();
    flush_all ();
    (* close_out lp_oc; *)
    close_out debug_oc

let default_log_file : string = "/tmp/lambdapi_lsp_log.txt"
