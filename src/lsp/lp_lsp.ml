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
let oint_field  name dict =
  Option.map_default U.to_int 0 List.(assoc_opt name dict)
let odict_field name dict =
  Option.get [] U.(to_option to_assoc
                      (Option.get `Null List.(assoc_opt name dict)))

module LIO = Lsp_io
module LSP = Lsp_base

(* --- didChange debouncing ------------------------------------------ *)
(* The main event loop is single-threaded; didChange triggers a full
   re-check, which can take seconds on large files. Under rapid typing
   we'd queue up one re-check per keystroke and fall further and
   further behind. The fix: read-ahead on stdin, and drop obsolete
   didChanges before running the check.
                                                                      *)

(* Messages read from stdin but not yet dispatched, held back so we
   can peek ahead at what's in flight. *)
let pending : J.t Queue.t = Queue.create ()

(* Drain every message immediately available (in our IO buffer or on
   the fd) into [pending]. The buffer-first check inside
   [LIO.bytes_pending] is critical: messages frequently land in the
   IO buffer past the current one, but [Unix.select] on the fd alone
   wouldn't see them. *)
let drain_stdin_nonblocking () : unit =
  while LIO.bytes_pending () do
    try Queue.add (LIO.read_request ()) pending
    with _ -> ()
  done

(* Return the next request, preferring already-drained ones over a
   fresh blocking read. *)
let read_next_or_block () : J.t =
  match Queue.take_opt pending with
  | Some m -> m
  | None -> LIO.read_request ()

(* True iff a later [textDocument/didChange] for [uri] is sitting in
   [pending]. If so, running a re-check for the current change is
   wasted work — the trailing one will trigger its own. *)
let pending_change_for_uri (uri : string) : bool =
  Queue.fold (fun acc msg ->
    acc ||
    (try
       let d = Yojson.Basic.Util.to_assoc msg in
       let mth = Yojson.Basic.Util.to_string (List.assoc "method" d) in
       mth = "textDocument/didChange" &&
       let p = Yojson.Basic.Util.to_assoc (List.assoc "params" d) in
       let document = Yojson.Basic.Util.to_assoc
         (List.assoc "textDocument" p) in
       Yojson.Basic.Util.to_string (List.assoc "uri" document) = uri
     with _ -> false))
    false pending

(* Walk a nested path of object keys; return the leaf or [None] if any
   segment is missing / has the wrong shape. *)
let rec json_path (j : J.t) (keys : string list) : J.t option =
  match keys with
  | [] -> Some j
  | k :: rest ->
    (match j with
     | `Assoc fields ->
       (match List.assoc_opt k fields with
        | Some v -> json_path v rest
        | None -> None)
     | _ -> None)

(** [path_of_file_uri uri] strips the [file://] scheme and percent-decodes
    the remainder. Returns [None] when [uri] is not a [file:] URI. *)
let path_of_file_uri (uri : string) : string option =
  if String.is_prefix "file://" uri then
    Some (Uri.pct_decode (String.sub uri 7 (String.length uri - 7)))
  else None

(* Request Handling: The client expects a reply *)
let do_initialize ofmt ~id params =
  (* Read clientCapabilities for features we gate on client support. *)
  let client_caps =
    try List.assoc "capabilities" params with Not_found -> `Null in
  let snippet_support =
    match json_path client_caps
            ["textDocument"; "completion"; "completionItem";
             "snippetSupport"]
    with
    | Some (`Bool b) -> b
    | _ -> false
  in
  let hierarchical_symbols =
    match json_path client_caps
            ["textDocument"; "documentSymbol";
             "hierarchicalDocumentSymbolSupport"]
    with
    | Some (`Bool b) -> b
    | _ -> false
  in
  LSP.snippet_support := snippet_support;
  LSP.hierarchical_symbols := hierarchical_symbols;
  (* Apply the workspace's [lambdapi.pkg] (if any) so module mappings
     are live before the first document is opened. [rootUri] is the
     pre-3.6 field; [workspaceFolders] is the current one — honour both
     when present. Per-file [Package.apply_config] still runs on every
     open, so this is strictly a bootstrap. *)
  let apply_folder uri =
    match path_of_file_uri uri with
    | Some p ->
      LIO.log_error "initialize" ("applying package config at " ^ p);
      Parsing.Package.apply_config p
    | None -> ()
  in
  (match List.assoc_opt "rootUri" params with
   | Some (`String uri) -> apply_folder uri
   | _ -> ());
  (match List.assoc_opt "workspaceFolders" params with
   | Some (`List folders) ->
     List.iter (fun f ->
       match f with
       | `Assoc fields ->
         (match List.assoc_opt "uri" fields with
          | Some (`String uri) -> apply_folder uri
          | _ -> ())
       | _ -> ()) folders
   | _ -> ());
  let msg = LSP.mk_reply ~id ~result:(
      `Assoc ["capabilities",
       `Assoc [
          "textDocumentSync", `Int 1
        ; "documentSymbolProvider", `Bool true
        ; "hoverProvider", `Bool true
        ; "definitionProvider", `Bool true
        ; "completionProvider", `Assoc [
            "triggerCharacters", `List [`String "."];
            "resolveProvider", `Bool true
          ]
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
    with Common.Error.Fatal(_pos, msg) ->
      (doc, Lp_doc.mk_error ~doc (Pos.file_start doc.uri) msg)
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
  (* Apply every content change to the in-memory text before deciding
     whether to re-check. With full-document sync each change is a
     whole new text, but we keep the fold so incremental sync can drop
     in later. *)
  let doc =
    List.fold_left
      (fun (doc : Lp_doc.t) change ->
        { doc with text = string_field "text" change })
      doc changes in
  Hashtbl.replace doc_table uri doc;
  (* Debounce: if a later didChange for this URI is already in flight,
     skip the re-check — the trailing change will trigger its own. *)
  drain_stdin_nonblocking ();
  if pending_change_for_uri uri then
    LIO.log_error "debounce"
      ("skipping check; later didChange pending for " ^ uri)
  else
    do_check_text ofmt ~doc

let do_close _ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in
  Hashtbl.remove doc_table doc_file;
  Hashtbl.remove completed_table doc_file

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
  let uri =
    if String.is_prefix "file://" file then file
    else "file://" ^ file
  in
  `Assoc [
      "uri", `String uri
    ; "range", LSP.mk_range pos
        ]

let kind_of_type tm =
  let open Term in
  let open Timed in
  let is_undef =
    Option.is_None !(tm.sym_def) && List.length !(tm.sym_rules) = 0 in
  match !(tm.sym_type) with
  | Vari _ ->
    13                         (* Variable *)
  | Type | Kind | Symb _ | _ when is_undef ->
    14                         (* Constant *)
  | _ ->
    12                         (* Function *)

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
    [symbol] (Function), [opaque symbol] (Function), and [inductive]
    (Enum with constructors as EnumMember children). Require/open,
    rules, builtins, queries, notations, etc. are skipped. *)
let document_symbols_of_nodes (nodes : Lp_doc.doc_node list) : J.t list =
  let open Parsing.Syntax in
  let range_of_pos p = LSP.mk_range p in
  let range_or_fallback (p : Pos.popt) (fallback : J.t) =
    match p with Some p -> range_of_pos p | None -> fallback
  in
  (* [nodes] is stored in reverse (head = most recent); restore
     top-to-bottom order for the outline. *)
  List.concat_map (fun ({ ast; _ } : Lp_doc.doc_node) ->
    match Pure.Command.get_pos ast with
    | None -> []
    | Some cmd_pos ->
      let cmd_range = range_of_pos cmd_pos in
      match Pure.Command.get_elt ast with
      | P_symbol s ->
        let sel = range_or_fallback s.p_sym_nam.pos cmd_range in
        [ mk_document_symbol
            ~name:s.p_sym_nam.elt ~kind:12   (* Function *)
            ~range:cmd_range ~selection_range:sel () ]
      | P_opaque qid ->
        let sel = range_or_fallback qid.pos cmd_range in
        let name = snd qid.elt in
        [ mk_document_symbol
            ~name ~kind:12                   (* Function *)
            ~range:cmd_range ~selection_range:sel () ]
      | P_inductive (_, _, inds) ->
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
    Pure.restore_time ss;
    let result =
      if !LSP.hierarchical_symbols then
        `List (document_symbols_of_nodes doc.Lp_doc.nodes)
      else
        let sym = Pure.get_symbols ss in
        let syms =
          Extra.StrMap.fold
            (fun _ s l ->
              let open Term in
              Option.map_default
                (fun p -> mk_syminfo file
                    (s.sym_name, s.sym_path, kind_of_type s, p) :: l) l s.sym_pos)
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
  List.find_opt (fun { ast; _ } ->
      let loc = Pure.Command.get_pos ast in
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
    let module_def path =
      let file = Library.(file_of_path path ^ lp_src_extension) in
      mk_definfo file (Pos.file_start file)
    in
    let sym_info =
      match get_symbol pt doc.map with
      | Some (qid, _) ->
        (match Pure.find_sym ss (Pos.none qid) with
         | None -> `Null
         | Some s when s.Term.sym_path = Sign.Ghost.path -> `Null
         | Some s ->
           let file =
             Library.(file_of_path s.Term.sym_path ^ lp_src_extension) in
           let pos = Option.get (Pos.file_start file) s.sym_pos in
           mk_definfo file pos)
      | None ->
        (* Fall back to module-path lookup for go-to-def on require/open. *)
        match get_symbol pt doc.path_map with
        | Some (path, _) -> module_def path
        | None -> `Null
    in
    let msg = LSP.mk_reply ~id ~result:sym_info in
    LIO.send_json ofmt msg

let hover_symInfo ofmt ~id params =
  let _, _, doc = grab_doc params in
  let ln, pos = get_textPosition params in
  let pt = Range.make_point (ln + 1) pos in

  let send contents range =
    let result = `Assoc ["contents", contents; "range", range] in
    LIO.send_json ofmt (LSP.mk_reply ~id ~result)
  in
  let send_null () =
    LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null)
  in

  try
    let ss = match doc.final with
      | Some ss -> ss
      | None -> raise (Error.fatal_no_pos "Root state is missing") in
    Pure.restore_time ss;

    match get_symbol pt doc.map with
    | None -> send_null ()
    | Some (qid, range) ->
      (match Pure.find_sym ss (Pos.none qid) with
       | None -> send_null ()
       | Some sym_found ->
         let sym_type = Format.asprintf "%a" Core.Print.sym_type sym_found in
         send (`String sym_type) (LSP.mk_range_of_interval range))
  with e ->
    LIO.log_error "hover_symInfo" (Printexc.to_string e);
    send_null ()

(* --- Completion ------------------------------------------------------- *)

(** CompletionItemKind for a declared symbol. *)
let completion_kind (tm : Term.sym) =
  let open Term in
  let open Timed in
  let is_undef =
    Option.is_None !(tm.sym_def) && List.length !(tm.sym_rules) = 0 in
  match tm.sym_prop with
  | Const -> 21                       (* Constant *)
  | Injec -> 3                        (* Function *)
  | _ when is_undef -> 21             (* Constant *)
  | _ -> 3                            (* Function *)

(** Tactic keywords offered as completions inside a proof. Each entry
    is [(name, detail, snippet)] — [snippet] is a TextMate-style
    template used when the client advertises [snippetSupport]. When
    the client doesn't, the label is inserted verbatim. The list
    should stay in sync with the [Syntax.p_tactic] cases handled in
    [Pure.Tactic.get_focus_pos]. *)
let tactic_completions : (string * string * string) list = [
  "admit",       "end proof as axiom",              "admit";
  "apply",       "apply a term to the goal",        "apply ${1:term}";
  "assume",      "introduce hypotheses",            "assume ${1:h}";
  "change",      "change the goal type",            "change ${1:type}";
  "eval",        "evaluate a term",                 "eval ${1:term}";
  "fail",        "always fail",                     "fail";
  "generalize",  "generalize a variable",           "generalize ${1:x}";
  "have",        "introduce an intermediate lemma", "have ${1:h}: ${2:type}";
  "induction",   "structural induction",            "induction";
  "refine",      "provide a partial proof term",    "refine ${1:term}";
  "reflexivity", "close goal by reflexivity",       "reflexivity";
  "remove",      "remove a hypothesis",             "remove ${1:h}";
  "rewrite",     "rewrite using an equation",       "rewrite ${1:eq}";
  "set",         "define a local abbreviation",     "set ${1:x} \xe2\x89\x94 ${2:term}";
  "simplify",    "simplify the goal",               "simplify";
  "solve",       "solve by unification",            "solve";
  "symmetry",    "swap sides of an equation",       "symmetry";
  "try",         "try a tactic; never fails",       "try ${1:tac}";
  "why3",        "dispatch to an external prover",  "why3";
]

let is_tactic_name n =
  List.exists (fun (tn, _, _) -> tn = n) tactic_completions

(** Hypotheses visible at the cursor inside a proof. Returns the
    focused goal's [(name, type_string)] list, or [[]] when no goal
    is active at that position. *)
let hyps_at_cursor (doc : Lp_doc.t) line character : (string * string) list =
  match get_node_at_pos doc line character with
  | None -> []
  | Some n ->
    (match closest_before (line + 1, character) n.Lp_doc.goals with
     | Some (goals, _) ->
       (match goals with (hyps, _) :: _ -> hyps | [] -> [])
     | None -> [])

let path_to_json (p : Path.t) : J.t =
  `List (List.map (fun s -> `String s) p)

let do_completion ofmt ~id params =
  let uri, line, character = get_docTextPosition params in
  let empty = `Assoc ["isIncomplete", `Bool false; "items", `List []] in
  match Hashtbl.find_opt completed_table uri with
  | None -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:empty)
  | Some doc ->
    match doc.Lp_doc.final with
    | None -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:empty)
    | Some ss ->
      Pure.restore_time ss;
      let syms = Pure.get_symbols ss in
      let in_proof =
        match get_node_at_pos doc line character with
        | Some n -> n.Lp_doc.goals <> []
        | None -> false
      in
      let items = ref [] in
      (* Symbols. `detail` is filled in on [completionItem/resolve]. *)
      Extra.StrMap.iter (fun name s ->
        (* Inside a proof, tactic keywords shadow symbols of the same
           name in the completion list: the user almost certainly
           means the tactic. *)
        if in_proof && is_tactic_name name then ()
        else
          let data = `Assoc [
              "kind", `String "symbol";
              "uri",  `String uri;
              "path", path_to_json s.Term.sym_path;
              "name", `String s.Term.sym_name;
          ] in
          items := `Assoc [
            "label", `String name;
            "kind",  `Int (completion_kind s);
            "data",  data;
          ] :: !items
      ) syms;
      if in_proof then begin
        (* Tactic keywords, with snippet insertions when supported. *)
        List.iter (fun (name, detail, snippet) ->
          let base = [
            "label", `String name;
            "kind",  `Int 14;                 (* Keyword *)
            "detail", `String detail;
            "sortText", `String ("0" ^ name);
          ] in
          let fields =
            if !LSP.snippet_support then
              base @
              [ "insertText", `String snippet
              ; "insertTextFormat", `Int 2 ]  (* Snippet *)
            else base
          in
          items := `Assoc fields :: !items
        ) tactic_completions;
        (* Hypotheses of the focused goal. *)
        List.iter (fun (hname, htype) ->
          items := `Assoc [
            "label", `String hname;
            "kind",  `Int 6;                  (* Variable *)
            "detail", `String htype;
            "sortText", `String ("1" ^ hname);
          ] :: !items
        ) (hyps_at_cursor doc line character)
      end;
      let result = `Assoc [
        "isIncomplete", `Bool false;
        "items", `List !items;
      ] in
      LIO.send_json ofmt (LSP.mk_reply ~id ~result)

(** Attach [detail] (and eventually other fields) to the completion
    item the client highlighted. The initial completion response is
    kept light by omitting per-symbol type strings; they're
    pretty-printed here, lazily, once per highlighted item. *)
let do_completion_resolve ofmt ~id params =
  let echo () =
    LIO.send_json ofmt (LSP.mk_reply ~id ~result:(`Assoc params))
  in
  match List.assoc_opt "data" params with
  | Some (`Assoc data) ->
    (match List.assoc_opt "kind" data with
     | Some (`String "symbol") ->
       let uri = try string_field "uri" data with _ -> "" in
       let name = try string_field "name" data with _ -> "" in
       let path =
         try List.map U.to_string (U.to_list (List.assoc "path" data))
         with _ -> []
       in
       (match Hashtbl.find_opt completed_table uri with
        | None -> echo ()
        | Some doc ->
          match doc.Lp_doc.final with
          | None -> echo ()
          | Some ss ->
            Pure.set_print_state ss;
            (match Pure.find_sym ss (Pos.none (path, name)) with
             | None -> echo ()
             | Some sym ->
               let type_str =
                 Format.asprintf "%a" Core.Print.sym_type sym in
               let fields =
                 ("detail", `String type_str) ::
                 List.remove_assoc "detail" params in
               LIO.send_json ofmt
                 (LSP.mk_reply ~id ~result:(`Assoc fields))))
     | _ -> echo ())
  | _ -> echo ()

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
    (try hover_symInfo ofmt ~id params
     with _ -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null))

  | "textDocument/definition" ->
    (try do_definition ofmt ~id params
     with _ -> LIO.send_json ofmt (LSP.mk_reply ~id ~result:`Null))

  | "textDocument/completion" ->
    (try do_completion ofmt ~id params
     with _ ->
       let empty = `Assoc ["isIncomplete", `Bool false; "items", `List []] in
       LIO.send_json ofmt (LSP.mk_reply ~id ~result:empty))

  | "completionItem/resolve" ->
    (try do_completion_resolve ofmt ~id params
     with _ ->
       LIO.send_json ofmt (LSP.mk_reply ~id ~result:(`Assoc params)))

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
    LIO.log_error "no_handler" msg

let process_input ofmt (com : J.t) =
  try dispatch_message ofmt (U.to_assoc com)
  with
  | U.Type_error (msg, obj) ->
    LIO.log_object msg obj
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "[BT]" bt;
    LIO.log_error "process_input" (Printexc.to_string exn);
    (* Send a null reply so the client doesn't hang *)
    let id = oint_field "id" (U.to_assoc com) in
    if id <> 0 then begin
      let msg = LSP.mk_reply ~id ~result:`Null in
      LIO.send_json ofmt msg
    end

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
    let com = read_next_or_block () in
    LIO.log_object "read" com;
    process_input oc com;
    F.pp_print_flush lp_fmt ();
    (* Soak up anything that arrived while we were busy so the
       debounce check in [do_change] sees a current view. *)
    drain_stdin_nonblocking ();
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
