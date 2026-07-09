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

open Lplib
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
let odict_field name dict =
  Option.get [] U.(to_option to_assoc
                      (Option.get `Null List.(assoc_opt name dict)))

module LIO = Lsp_io
module LSP = Lsp_base

(* Walk a nested path of object keys; return the leaf or [None] if any
   segment is missing / has the wrong shape. *)
let json_path (j : J.t) (keys : string list) : J.t option =
  List.fold_left
    (fun j k ->
       match j with
       | Some (`Assoc fields) -> List.assoc_opt k fields
       | _ -> None)
    (Some j) keys

(** [path_of_file_uri uri] strips the [file://] scheme and percent-decodes
    the remainder. Returns [None] when [uri] is not a [file:] URI. *)
let path_of_file_uri (uri : string) : string option =
  if String.is_prefix "file://" uri then
    Some (Uri.pct_decode (String.sub uri 7 (String.length uri - 7)))
  else None

(* Client capabilities we gate features on, read from the [initialize]
   request. *)

(* [textDocument.completion.completionItem.snippetSupport]: snippet
   syntax allowed in completion [insertText]. *)
let snippet_support = ref false

(* [textDocument.documentSymbol.hierarchicalDocumentSymbolSupport]:
   hierarchical [DocumentSymbol[]] responses understood; when false,
   fall back to flat [SymbolInformation[]]. *)
let hierarchical_symbols = ref false

(* [textDocument.completion.completionItem.documentationFormat]
   includes "markdown": completion docs may be sent as markdown
   [MarkupContent] (plain strings render literally otherwise). *)
let markdown_completion_docs = ref false

(* Request Handling: The client expects a reply *)
let do_initialize ofmt ~id params =
  (* Read clientCapabilities for features we gate on client support. *)
  let client_caps =
    Option.get `Null (List.assoc_opt "capabilities" params) in
  let cap_bool path =
    match json_path client_caps path with
    | Some (`Bool b) -> b
    | _ -> false
  in
  snippet_support :=
    cap_bool
      ["textDocument"; "completion"; "completionItem"; "snippetSupport"];
  hierarchical_symbols :=
    cap_bool
      ["textDocument"; "documentSymbol";
       "hierarchicalDocumentSymbolSupport"];
  markdown_completion_docs :=
    (match json_path client_caps
             ["textDocument"; "completion"; "completionItem";
              "documentationFormat"]
     with
     | Some (`List fmts) -> List.mem (`String "markdown") fmts
     | _ -> false);
  (* Apply the workspace's [lambdapi.pkg] (if any) so module mappings
     are live before the first document is opened. [rootUri] is the
     pre-3.6 field; [workspaceFolders] is the current one — clients
     typically send BOTH for the same directory, so deduplicate. And a
     failure (e.g. "module path already mapped") must never abort
     [initialize] — the client would kill the server and retry in a
     loop; per-file [Package.apply_config] still runs on every open. *)
  let apply_folder uri =
    match path_of_file_uri uri with
    | Some p ->
      (try
         LIO.log_error "initialize" ("applying package config at " ^ p);
         Parsing.Package.apply_config p
       with e ->
         LIO.log_error "initialize"
           ("package config skipped: " ^ Printexc.to_string e))
    | None -> ()
  in
  let root_folders =
    match List.assoc_opt "rootUri" params with
    | Some (`String uri) -> [uri]
    | _ -> []
  in
  let ws_folders =
    match List.assoc_opt "workspaceFolders" params with
    | Some (`List folders) ->
      List.filter_map
        (fun f ->
           match json_path f ["uri"] with
           | Some (`String uri) -> Some uri
           | _ -> None)
        folders
    | _ -> []
  in
  List.iter apply_folder
    (List.sort_uniq Stdlib.compare (root_folders @ ws_folders));
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
  let doc, diags =
    try
      Lp_doc.check_text ~doc
    with Common.Error.Fatal(_pos, msg, err_desc) ->
      (doc, Lp_doc.mk_error ~doc (Pos.file_start doc.uri)
              (msg ^ "\n" ^ err_desc))
  in
  Hashtbl.replace doc_table doc.uri doc;
  Hashtbl.replace completed_table doc.uri doc;
  LIO.send_json ofmt @@ diags

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
  LIO.log_error "checking file"
    (uri ^ " / version: " ^ (string_of_int version));
  let doc = Hashtbl.find doc_table uri in
  let doc = { doc with Lp_doc.version; } in
  (* With full-document sync each change carries the whole new text;
     the fold applies them all, then a single re-check runs. *)
  let doc =
    List.fold_left
      (fun (doc : Lp_doc.t) change ->
        { doc with text = string_field "text" change })
      doc changes in
  do_check_text ofmt ~doc

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

(* [file] is a plain filesystem path (as produced by
   [Library.file_of_path]), never a URI. *)
let mk_definfo file pos =
  `Assoc [
      "uri", `String ("file://" ^ file)
    ; "range", LSP.mk_range pos
        ]

(* No LSP SymbolKind matches lambdapi's notions (axiom, constructor,
   definable symbol, theorem, …), so we do not classify: every symbol
   is reported as Function, the least surprising icon. (SymbolKind is
   a mandatory field; completions simply omit their optional one.) *)
let symbol_kind = 12                                       (* Function *)

let mk_document_symbol ?(children=[]) ~name ~kind ~range ~selection_range ()
  : J.t =
  `Assoc [
    "name", `String name;
    "kind", `Int kind;
    "range", range;
    "selectionRange", selection_range;
    "children", `List children;
  ]

(** Build hierarchical [DocumentSymbol[]] from the parsed AST. Only
    declarations that introduce user-visible symbols are emitted:
    [symbol] (Function) and [inductive] (Enum with constructors as
    EnumMember children). Require/open, rules, builtins, queries,
    notations, etc. are skipped. *)
let document_symbols_of_nodes (nodes : Lp_doc.doc_node list) : J.t list =
  let open Parsing.Syntax in
  let range_or_fallback (p : Pos.popt) (fallback : J.t) =
    match p with Some p -> LSP.mk_range p | None -> fallback
  in
  (* [nodes] is stored in reverse (head = most recent); restore
     top-to-bottom order for the outline. *)
  List.concat_map (fun ({ cmd; _ } : Lp_doc.doc_node) ->
    match Pure.Command.get_pos cmd with
    | None -> []
    | Some cmd_pos ->
      let cmd_range = LSP.mk_range cmd_pos in
      match Pure.Command.get_elt cmd with
      | P_symbol s ->
        let sel = range_or_fallback s.p_sym_nam.pos cmd_range in
        [ mk_document_symbol
            ~name:s.p_sym_nam.elt ~kind:symbol_kind
            ~range:cmd_range ~selection_range:sel () ]
      | P_inductive (_, _, _, inds) ->
        List.map (fun (ind : p_inductive) ->
          let (iname, _, cons) = ind.Pos.elt in
          let ind_range = range_or_fallback ind.Pos.pos cmd_range in
          let sel = range_or_fallback iname.pos ind_range in
          let children = List.map (fun (cname, _ctyp) ->
            let crange = range_or_fallback cname.Pos.pos ind_range in
            mk_document_symbol
              ~name:cname.Pos.elt ~kind:22   (* EnumMember *)
              ~range:crange ~selection_range:crange ()
          ) cons in
          mk_document_symbol
            ~name:iname.elt ~kind:10         (* Enum *)
            ~range:ind_range ~selection_range:sel ~children ()
        ) inds
      | _ -> []
  ) (List.rev nodes)

let do_symbols ofmt ~id params =
  let file, _, doc = grab_doc params in
  match doc.final with
  | None    ->
    let msg = LSP.mk_reply ~id ~result:`Null in
    LIO.send_json ofmt msg
  | Some ss ->
    let result =
      if !hierarchical_symbols then
        (* Built from the parsed AST alone; no signature state needed. *)
        `List (document_symbols_of_nodes doc.Lp_doc.nodes)
      else
        let () = Pure.restore_time ss in
        let sym = Pure.get_symbols ss in
        let syms =
          Extra.StrMap.fold
            (fun _ s l ->
              let open Term in
              Option.map_default
                (fun p ->
                  mk_syminfo file
                    (s.sym_name, s.sym_path, symbol_kind, p) :: l)
                l s.sym_pos)
            sym [] in
        `List syms
    in
    LIO.send_json ofmt (LSP.mk_reply ~id ~result)


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

(** [closest_before (line, pos) objs] returns the element in [objs] with
largest position which is before [(line, pos)]*)
let closest_before : int * int -> ('a * Pos.popt) list ->
                     ('a * Pos.popt) option =
  fun (line, pos) (objs: ('a * Pos.popt) list) ->
  let objs =
    List.filter (fun (_, objpos) ->
        match objpos with
        | None -> false
        | Some objpos ->
            let open Pos in
            compare (objpos.start_line, objpos.start_col) (line, pos) <= 0)
      objs
  in
  let closer (acc: ('a * Pos.popt) option) (obj : 'a * Pos.popt) =
    let open Pos in
    match (snd obj) with
    | None -> acc
    | Some objpos ->
        match acc with
        | None -> Some obj
        | Some (_, accposopt) ->
            match accposopt with
            | None -> Some obj
            | Some accpos ->
                let comp =
                  compare (objpos.start_line, objpos.start_col)
                    (accpos.start_line, accpos.start_col)
                in
                if comp <= 0 then acc else Some obj
  in
  List.fold_left closer None objs

let in_range ?loc (line, pos) =
  match loc with
  | None -> false
  | Some Pos.{start_line; start_col; end_line; end_col; _} ->
    let line = line + 1 in
    (compare (start_line, start_col) (line, pos)) *
    (compare (end_line, end_col) (line, pos)) <= 0

let get_node_at_pos doc line pos =
  let open Lp_doc in
  List.find_opt (fun { cmd; _ } ->
      let loc = Pure.Command.get_pos cmd in
      in_range ?loc (line,pos)
    ) doc.Lp_doc.nodes

(** [get_first_error doc] returns the first error inferred from doc.logs *)
let get_first_error doc =
  List.fold_left (fun acc b ->
    let ((sev, _), bpos) = b in
    if sev != 1 then acc else
      match acc with
      | None -> Some b
      | Some ((_, _), apos) ->
        let open Pos in
        match apos with None -> Some b | Some apos ->
        match bpos with None -> acc | Some bpos ->
        if compare (apos.start_line, apos.start_col)
                   (bpos.start_line, bpos.start_col) <= 0 then
          acc else Some b) None doc.Lp_doc.logs

let rec get_goals ~doc ~line ~pos =
  let (line,pos) =
    match get_first_error doc with
    | Some ((_,_), Some errpos) ->
      let errpos = (errpos.start_line, errpos.start_col) in
      if compare errpos (line, pos) <= 0 then errpos else (line, pos)
    | _ -> (line,pos)
  in
  let node = get_node_at_pos doc line pos in
  let goals = match node with
    | None -> Some([], None)
    | Some n ->
        closest_before (line+1, pos) n.goals in
  match goals with
    | None -> begin match node with
              | None   -> None
              | Some _ -> get_goals ~doc ~line:(line-1) ~pos:0 end
    | Some (v,_) -> Some v

let get_logs ~doc ~line ~pos : string =
  let line = line+1 in
  let end_limit =
    match get_first_error doc with
    | Some ((_,_), Some errpos) ->
      let errpos = (errpos.start_line, errpos.start_col) in
      if compare errpos (line, pos) <= 0 then errpos else (line, pos)
    | _ -> (line,pos)
  in
  let logs =
    List.filter_map
      (fun ((_,msg),loc) ->
         match loc with
         | Some Pos.{start_line; start_col; _}
           when compare (start_line,start_col) end_limit <= 0 -> Some msg
         | _ -> None)
      doc.Lp_doc.logs
  in
  String.concat "" logs

let do_goals ofmt ~id params =
  let uri, line, pos = get_docTextPosition params in
  let doc = Hashtbl.find completed_table uri in
  let goals = get_goals ~doc ~line ~pos in
  let logs = get_logs ~doc ~line ~pos in
  let result = LSP.json_of_goals goals ~logs in
  let msg = LSP.mk_reply ~id ~result in
  LIO.send_json ofmt msg


let get_symbol : Range.point -> 'a RangeMap.t -> ('a * Range.t) option
= fun pos doc ->

  let open RangeMap in

  match (find pos doc) with
  | None -> None
  | Some(interval, value) -> Some (value, interval)

let do_definition ofmt ~id params =

  let _, _, doc = grab_doc params in
  match doc.final with
  | None    ->
    let msg = LSP.mk_reply ~id ~result:`Null in
    LIO.send_json ofmt msg
  | Some ss ->
    Pure.restore_time ss;
    let ln, pos = get_textPosition params in

    (* Lines sent by the client start at 0 *)
    let pt = Range.make_point (ln + 1) pos in
    let sym_info =
      match get_symbol pt doc.map with
      | None ->
        LIO.log_error "do_definition" "no symbol at point"; `Null
      | Some (qid, _) ->
        LIO.log_error "do_definition" (snd qid);
        match Pure.find_sym ss qid with
        | None -> `Null
        (* Ghost symbols (internal symbols used e.g. for unification
           rules and string literals) have no user-facing definition
           site one could jump to. *)
        | Some s when s.Term.sym_path = Sign.Ghost.path -> `Null
        | Some s ->
          let file =
            Library.(file_of_path s.Term.sym_path ^ lp_src_extension) in
          let pos = Option.get (Pos.file_start file) s.sym_pos in
          mk_definfo file pos
    in
    let msg = LSP.mk_reply ~id ~result:sym_info in
    LIO.send_json ofmt msg

let hover_symInfo ofmt ~id params =
  let _, _, doc = grab_doc params in
  let ln, pos = get_textPosition params in
  let pt = Range.make_point (ln + 1) pos in
  LIO.log_error "hover_symInfo" (Range.point_to_string pt);

  let send_null () =
    LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null)
  in

  try
    let ss = match doc.final with
      | Some ss -> ss
      | None ->
        raise (Error.fatal_no_pos "Final state is missing: the document \
                                   was never successfully loaded") in
    Pure.restore_time ss;

    match get_symbol pt doc.map with
    | None -> send_null ()
    | Some (qid, range) ->
      match Pure.find_sym ss qid with
      | None -> send_null ()
      | Some sym_found ->
        let sym_type = Format.asprintf "%a" Core.Print.sym_type sym_found in
        let result = `Assoc [ "contents", `String sym_type
                            ; "range", LSP.mk_range_of_interval range ] in
        LIO.send_json ofmt (LSP.mk_reply ~id ~result)
  with e ->
    LIO.log_error "hover_symInfo" (Printexc.to_string e);
    send_null ()

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
  (* The "id" member is kept verbatim (JSON-RPC ids may be numbers or
     strings) and echoed back as-is in replies. *)
  let id     = Option.get `Null (List.assoc_opt "id" dict) in
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
    (try hover_symInfo ofmt ~id params
     with _ -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null))

  | "textDocument/definition" ->
    (try do_definition ofmt ~id params
     with _ -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null))

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
  | "initialized" ->
    ()
  | msg ->
    (* Requests carry an id; notifications don't. For requests we must
       reply with JSON-RPC MethodNotFound so the client doesn't wait
       forever. Notifications get logged and dropped, matching the
       spec's "no response" rule. *)
    LIO.log_error "no_handler" msg;
    if List.mem_assoc "id" dict then
      LIO.send_json ofmt
        (LSP.mk_error_reply ~id ~code:(-32601)
           ~msg:("Method not found: " ^ msg))

let process_input ofmt (com : J.t) =
  try dispatch_message ofmt (U.to_assoc com)
  with
  | U.Type_error (msg, obj) ->
    LIO.log_object msg obj
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[BT]" bt;
    LIO.log_error "process_input" (Printexc.to_string exn);
    (* Send a null reply so the client doesn't hang. Requests carry an
       "id" field; note that id 0 is a valid request id (Zed numbers
       its first request 0), so key on the field's presence. *)
    let dict = U.to_assoc com in
    match List.assoc_opt "id" dict with
    | Some id -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null)
    | None -> ()

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
  Error.err_fmt := lp_fmt;
  (* Console.verbose := 4; *)

  let rec loop () =
    let com = LIO.read_request stdin in
    LIO.log_object "read" com;
    process_input oc com;
    F.pp_print_flush lp_fmt ();
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
