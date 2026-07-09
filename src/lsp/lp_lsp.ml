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
        (* "." separates module-path and qualified-name segments; the
           completion handler resolves both contexts (and stays quiet
           on a dot-trigger anywhere else). *)
        ; "completionProvider",
          `Assoc [ "resolveProvider", `Bool true
                 ; "triggerCharacters", `List [`String "."] ]
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

let find_node_at_pos nodes line pos =
  let open Lp_doc in
  List.find_opt (fun { cmd; _ } ->
      let loc = Pure.Command.get_pos cmd in
      in_range ?loc (line,pos)
    ) nodes

let get_node_at_pos doc line pos =
  find_node_at_pos doc.Lp_doc.nodes line pos

(* --- Cursor context: proof scripts, raw tokens, tactic docs -------- *)

(* Like [get_node_at_pos], but falling back to the nodes of the last
   parse-error-free check. A mid-edit text (a partial tactic name,
   say) fails to parse, dropping the command being edited from
   [nodes] — exactly when completion and hover need its proof
   context. [good_nodes] equals [nodes] whenever the text parses, so
   the fallback only ever serves stale data while the text is broken;
   edits happen within a line, so its line-based positions stay valid
   until the next clean parse. *)
let get_context_node doc line pos =
  match get_node_at_pos doc line pos with
  | Some n -> Some n
  | None -> find_node_at_pos doc.Lp_doc.good_nodes line pos

(* Identifier-ish token at the (0-based) [line]/[col] of [doc]'s text:
   the maximal run of non-delimiter code points around the cursor.
   Columns are counted in code points, matching the position handling
   in the rest of the server. Being text-based, it also works in
   regions the checker never reached (mid-edit text, code past a
   parse error). *)
(* Byte offset of each code point of [str], with the total length as
   a final sentinel. *)
let codepoint_offsets (str : string) : int array =
  let offs = ref [] and i = ref 0 in
  let n = String.length str in
  while !i < n do
    offs := !i :: !offs;
    i := !i + Uchar.utf_decode_length (String.get_utf_8_uchar str !i)
  done;
  Array.of_list (List.rev (n :: !offs))

(* Number of code points of [s]. *)
let cp_len (s : string) : int = Array.length (codepoint_offsets s) - 1

(** [line_prefix doc line col] is the text of the (0-based) [line] of
    [doc] before the cursor column [col] (counted in code points,
    like every position in the server). *)
let line_prefix (doc : Lp_doc.t) line col : string option =
  match List.nth_opt (String.split_on_char '\n' doc.Lp_doc.text) line with
  | None -> None
  | Some str ->
    let offs = codepoint_offsets str in
    let ncp = Array.length offs - 1 in
    let col = if col < 0 then 0 else if col > ncp then ncp else col in
    Some (String.sub str 0 offs.(col))

let token_at_pos (doc : Lp_doc.t) line col : string option =
  match List.nth_opt (String.split_on_char '\n' doc.Lp_doc.text) line with
  | None -> None
  | Some str ->
    let offs = codepoint_offsets str in
    let ncp = Array.length offs - 1 in
    (* Delimiters are ASCII; a multi-byte code point (first byte
       [>= '\x80']) always belongs to a token. *)
    let is_delim k =
      match str.[offs.(k)] with
      | ' ' | '\t' | '\r' | '(' | ')' | '[' | ']' | '{' | '}'
      | ';' | ',' | '"' | '.' | ':' | '@' -> true
      | _ -> false
    in
    if col < 0 || col >= ncp || is_delim col then None
    else
      let s = ref col and e = ref col in
      while !s > 0 && not (is_delim (!s - 1)) do decr s done;
      while !e + 1 < ncp && not (is_delim (!e + 1)) do incr e done;
      Some (String.sub str offs.(!s) (offs.(!e + 1) - offs.(!s)))

(* [begin_pos_of doc n] is the position (1-based line, code point
   column) of the [begin] keyword of [n]'s command in [doc]'s current
   text, if any. [begin] is a reserved word, so the first
   word-delimited occurrence within the command's span opens the
   proof script. *)
let begin_pos_of (doc : Lp_doc.t) (n : Lp_doc.doc_node)
  : (int * int) option =
  match Pure.Command.get_pos n.Lp_doc.cmd with
  | None -> None
  | Some Pos.{start_line; end_line; _} ->
    let lines = String.split_on_char '\n' doc.Lp_doc.text in
    let delim c =
      match c with
      | ' ' | '\t' | '\r' | '(' | ')' | '[' | ']' | '{' | '}'
      | ';' | ',' | '"' | '.' | ':' | '@' -> true
      | _ -> false
    in
    let find_in_line l =
      match List.nth_opt lines (l - 1) with
      | None -> None
      | Some str ->
        let len = String.length str in
        let rec search i =
          if i + 5 > len then None
          else if String.sub str i 5 = "begin"
               && (i = 0 || delim str.[i - 1])
               && (i + 5 = len || delim str.[i + 5])
          then
            (* Byte index to code point column ("b" is ASCII, so it
               sits on a code point boundary). *)
            let offs = codepoint_offsets str in
            let rec cp j = if offs.(j) = i then j else cp (j + 1) in
            Some (l, cp 0)
          else search (i + 1)
        in
        search 0
    in
    let rec scan l =
      if l > end_line then None
      else match find_in_line l with
        | Some p -> Some p
        | None -> scan (l + 1)
    in
    scan start_line

(* True iff the cursor is inside the proof script of the command at
   the cursor. Carrying a proof ([p_sym_prf]) is not enough: the
   command's span also covers the statement (name, type), which is
   not a proof position — require the cursor to be at or after the
   [begin] keyword. *)
let in_proof_at (doc : Lp_doc.t) line character : bool =
  match get_context_node doc line character with
  | Some n ->
    (match Pure.Command.get_elt n.Lp_doc.cmd with
     | Parsing.Syntax.P_symbol {p_sym_prf = Some _; _} ->
       (match begin_pos_of doc n with
        | Some bpos -> compare bpos (line + 1, character) <= 0
        | None -> false)
     | _ -> false)
  | None -> false

(* --- Completion context ------------------------------------------- *)

(* Complete whitespace-separated words of [s], and the token still
   being typed (empty when [s] ends in whitespace). *)
let words_and_partial (s : string) : string list * string =
  let s = String.map (fun c -> if c = '\t' then ' ' else c) s in
  match List.rev (String.split_on_char ' ' s) with
  | [] -> [], ""
  | partial :: rest ->
    List.rev (List.filter (fun w -> w <> "") rest), partial

(** Cursor context for completion, determined lexically from the
    line before the cursor. Only the contexts the parser's follow
    sets cannot provide remain here: those about the partial token
    being typed (module paths, qualified names, flag names) and the
    ranking of hypotheses in tactic arguments; keyword membership
    itself comes from the grammar (see [follow_at]). *)
type completion_context =
  | Ctx_require of string * int
    (** Module path of a [require]/[open]: the typed partial path
        and its start column. *)
  | Ctx_qualified of string * string
    (** Dotted token before the cursor: the module part (before the
        last dot) and the partial name after it. *)
  | Ctx_flag_name       (** Inside the string argument of [flag]. *)
  | Ctx_tactic_arg
    (** Argument of a tactic that names existing hypotheses. *)
  | Ctx_default

(* Tactics whose argument commonly mentions hypotheses. *)
let arg_tactics = ["apply"; "refine"; "rewrite"; "remove"; "generalize"]

(* Symbol modifiers and their sides. Repeating one is grammatical,
   so follow sets keep offering them; it is never useful, so the
   already-typed ones are filtered from completions. *)
let modifier_words =
  ["left"; "right"; "associative"; "commutative"; "constant";
   "injective"; "opaque"; "private"; "protected"; "sequential"]

(* [qualified_of partial] splits the dotted token ending [partial] at
   its last dot: [Some ("Stdlib.Nat", "ze")] for ["(Stdlib.Nat.ze"].
   [None] when there is no dot or nothing before it. *)
let qualified_of (partial : string) : (string * string) option =
  let is_delim c = String.contains "()[]{};,\":@" c in
  let start = ref 0 in
  String.iteri (fun i c -> if is_delim c then start := i + 1) partial;
  let tok =
    String.sub partial !start (String.length partial - !start) in
  match String.rindex_opt tok '.' with
  | Some i when i > 0 ->
    Some (String.sub tok 0 i,
          String.sub tok (i + 1) (String.length tok - i - 1))
  | _ -> None

let completion_context (doc : Lp_doc.t) line col : completion_context =
  match line_prefix doc line col with
  | None -> Ctx_default
  | Some prefix ->
    let words, partial = words_and_partial prefix in
    (* [require] accepts several paths; [as] switches to an alias
       name and [;] ends the command. *)
    let path_words ws =
      List.for_all
        (fun w -> w = "open"
                  || (w <> "as" && not (String.contains w ';')))
        ws
    in
    let quotes =
      String.fold_left
        (fun n c -> if c = '"' then n + 1 else n) 0 prefix
    in
    match words with
    | ("require" | "open") :: rest
    | "private" :: ("require" | "open") :: rest
      when path_words rest ->
      Ctx_require (partial, col - cp_len partial)
    | "flag" :: _ when quotes = 1 -> Ctx_flag_name
    | _ ->
      match qualified_of partial with
      | Some (mpath, name) -> Ctx_qualified (mpath, name)
      | None ->
        match words with
        | t :: _ when List.mem t arg_tactics -> Ctx_tactic_arg
        | _ -> Ctx_default

(* [doc] text before the cursor at (0-based) [line],[col] counted in
   code points, minus the partial word ending at the cursor: what the
   parser should see to tell what may come next (the client filters
   the items against the typed word itself). Word boundaries are the
   delimiters of [token_at_pos]; a multi-byte code point always
   belongs to a word. *)
let doc_prefix (doc : Lp_doc.t) line col : string =
  let cur =
    match line_prefix doc line col with
    | None -> ""
    | Some prefix ->
      let is_delim = function
        | ' ' | '\t' | '\r' | '(' | ')' | '[' | ']' | '{' | '}'
        | ';' | ',' | '"' | '.' | ':' | '@' -> true
        | _ -> false
      in
      let i = ref (String.length prefix) in
      while !i > 0 && not (is_delim prefix.[!i - 1]) do decr i done;
      String.sub prefix 0 !i
  in
  let lines = String.split_on_char '\n' doc.Lp_doc.text in
  let rec before i = function
    | l :: ls when i < line -> l :: before (i + 1) ls
    | _ -> []
  in
  String.concat "\n" (before 0 lines @ [cur])

(** Tokens the grammar accepts at the cursor, from the parser: the
    command starters between commands, the follow set of the
    truncated command within one, and [] when the text before the
    cursor has a syntax error (a broken edit earlier in the file) —
    callers then fall back to context-blind items. *)
let follow_at (doc : Lp_doc.t) line col : Parsing.LpLexer.token list =
  Pure.expected_tokens (doc_prefix doc line col)

(* Module paths under the current library mappings (the workspace
   package and every map-dir), found by scanning the mapped
   directories for source files. *)
let module_path_candidates () : string list =
  let out = ref [] in
  let rec scan prefix dir depth =
    if depth > 0 then
      match Sys.readdir dir with
      | exception Sys_error _ -> ()
      | entries ->
        Array.iter (fun e ->
          if e <> "" && e.[0] <> '.' then
            let p = Filename.concat dir e in
            if (try Sys.is_directory p with Sys_error _ -> false) then
              scan (prefix @ [e]) p (depth - 1)
            else
              List.iter (fun ext ->
                match Filename.chop_suffix_opt ~suffix:ext e with
                | Some base ->
                  out := String.concat "." (prefix @ [base]) :: !out
                | None -> ())
                [".lp"; ".dk"; ".lpo"])
          entries
  in
  Library.iter (fun mp dir -> scan mp dir 8);
  List.sort_uniq Stdlib.compare !out

(* Raw LSP range on one line (character units as sent by clients). *)
let mk_char_range line scol ecol : J.t =
  `Assoc [
    "start", `Assoc ["line", `Int line; "character", `Int scol];
    "end",   `Assoc ["line", `Int line; "character", `Int ecol];
  ]

(* Completion items replacing the typed [partial] (running from
   [start_col] to the cursor) by a full module path. The explicit
   [textEdit] matters: "." is not a word character in editors, so a
   plain label would be inserted after the last dot. *)
let mk_module_path_items ~line ~start_col ~cursor_col partial
  : J.t list =
  module_path_candidates ()
  |> List.filter (String.is_prefix partial)
  |> List.map (fun mp ->
      `Assoc [
        "label", `String mp;
        "kind", `Int 9;                          (* Module *)
        "filterText", `String mp;
        "textEdit", `Assoc
          [ "range", mk_char_range line start_col cursor_col
          ; "newText", `String mp ];
      ])

(* Completion items for the qualified name [mstr].[partial]: the
   non-private symbols of that module (resolving a [require as]
   alias), plus the next segments of loaded module paths extending
   it. Only loaded (i.e. required) modules can be referenced, so no
   filesystem scan here. The client inserts after the dot, so plain
   labels are enough. *)
let mk_qualified_items ss uri (mstr : string) : J.t list =
  let seg = String.split_on_char '.' mstr in
  let path =
    match seg with
    | [a] ->
      (match Extra.StrMap.find_opt a (Pure.get_aliases ss) with
       | Some p -> p
       | None -> seg)
    | _ -> seg
  in
  let loaded = Timed.(!) Sign.loaded in
  let sym_items =
    match Path.Map.find_opt path loaded with
    | None -> []
    | Some sign ->
      Extra.StrMap.fold (fun name (s : Term.sym) acc ->
          if s.Term.sym_expo = Term.Privat then acc
          else
            `Assoc [
              "label", `String name;
              "data", `Assoc
                [ "kind", `String "qualified"
                ; "uri",  `String uri
                ; "path", `String (String.concat "." path) ];
            ] :: acc)
        (Timed.(!) sign.Sign.sign_symbols) []
  in
  let rec list_is_prefix xs ys =
    match xs, ys with
    | [], _ -> true
    | x :: xs, y :: ys -> x = y && list_is_prefix xs ys
    | _, [] -> false
  in
  let n = List.length path in
  let segments =
    Path.Map.fold (fun p _ acc ->
        if list_is_prefix path p then
          match List.nth_opt p n with
          | Some seg -> seg :: acc
          | None -> acc
        else acc)
      loaded []
  in
  let seg_items =
    List.map (fun seg -> `Assoc ["label", `String seg; "kind", `Int 9])
      (List.sort_uniq Stdlib.compare segments)
  in
  sym_items @ seg_items

(** Tactic keywords offered as completions inside a proof and
    documented on hover. Each entry is [(name, detail, doc, snippet)]:
    [detail] is a one-line summary shown next to the completion label,
    [doc] the fuller documentation (sourced from [doc/tactics.rst],
    [doc/tacticals.rst] and [doc/equality.rst]) shown in the completion
    docs panel and on hover, and [snippet] a TextMate-style template
    used when the client advertises [snippetSupport] (otherwise the
    label is inserted verbatim). Covers every tactic documented in
    those files — enforced by the test suite, which extracts the
    documented names and checks them against this list. Queries,
    which double as tactics ([P_tac_query]), live in
    [query_completions]. [P_tac_and] is deliberately absent: it has
    no concrete syntax (only built internally by [eval]). *)
let tactic_completions : (string * string * string * string) list = [
  "admit", "discharge goal as axiom",
  "Adds new symbols (axioms) to the environment proving the focused goal.",
  "admit";

  "all_hyps", "apply a term to every hypothesis",
  "`all_hyps t` (with `t : Π p, Prf p → T`) applies `t _ xₙ`, …, \
   `t _ x₁` on the hypotheses `x₁ … xₙ`, ignoring failing calls; \
   fails if every call failed.",
  "all_hyps ${1:term}";

  "apply", "apply a term to the goal",
  "`apply t` refines the current goal with `t _ … _`, generating one \
   subgoal for each argument that cannot be inferred.",
  "apply ${1:term}";

  "assume", "introduce hypotheses",
  "If the focused goal is of the form `Π x₁ … xₙ, T`, then \
   `assume h₁ … hₙ` replaces it by `T` with each `xᵢ` replaced by \
   `hᵢ`.",
  "assume ${1:h}";

  "assumption", "close goal by an hypothesis",
  "Proves the current goal if it is (an instance of) an hypothesis.",
  "assumption";

  "change", "change the goal type",
  "`change t` replaces the current goal `u` by `t`, provided \
   `t ≡ u`.",
  "change ${1:type}";

  "eval", "interpret a term as a tactic",
  "`eval t` normalizes the term `t` and interprets the result as a \
   tactic expression built from the tactic builtins.",
  "eval ${1:term}";

  "fail", "always fail",
  "Always fails. Useful to stop at a particular point while \
   developing a proof.",
  "fail";

  "first_hyp", "apply a term to hypotheses until one succeeds",
  "`first_hyp t` (with `t : Π p, Prf p → T`) applies `t _ xₙ` on the \
   last hypothesis; if the goal is not solved, tries the next \
   hypothesis, and so on, failing if none succeeds.",
  "first_hyp ${1:term}";

  "focus", "move goal n to the front",
  "`focus n` moves the n-th goal (`n ≥ 2`) to position 1.",
  "focus ${1:n}";

  "generalize", "generalize a variable",
  "If the focused goal is `x₁:A₁, …, y₁:B₁, …, yₚ:Bₚ ⊢ U`, then \
   `generalize y₁` transforms it into \
   `x₁:A₁, … ⊢ Π y₁:B₁, …, Π yₚ:Bₚ, U`.",
  "generalize ${1:x}";

  "have", "introduce an intermediate lemma",
  "`have x: t` generates a new goal for `t`, then lets you prove the \
   focused goal with the additional hypothesis `x: t`.",
  "have ${1:h}: ${2:type}";

  "induction", "structural induction",
  "If the focused goal is of the form `Π x:I, …` with `I` an \
   inductive type, refines it by applying the induction principle \
   of `I`.",
  "induction";

  "orelse", "try a tactic, else another",
  "`orelse t₁ t₂` applies `t₁`; if `t₁` fails, applies `t₂`.",
  "orelse ${1:tac1} ${2:tac2}";

  "refine", "provide a partial proof term",
  "`refine t` instantiates the focused goal by `t`, which may \
   contain underscores `_` and metavariable names `?n`; \
   metavariables that cannot be solved become new goals.",
  "refine ${1:term}";

  "reflexivity", "close goal by reflexivity",
  "Solves a goal of the form `Π x₁, …, Π xₙ, P (t = u)` when \
   `t ≡ u`.",
  "reflexivity";

  "remove", "remove a hypothesis",
  "`remove h₁ … hₙ` erases the hypotheses `h₁ … hₙ` from the \
   context; the goal and the remaining hypotheses must not depend on \
   them.",
  "remove ${1:h}";

  "repeat", "repeat a tactic",
  "`repeat t` applies `t` on the first goal until the number of \
   goals decreases.",
  "repeat ${1:tac}";

  "rewrite", "rewrite using an equation",
  "`rewrite t` rewrites the goal with an equation \
   `t : Π x₁ … xₙ, P (l = r)` from left to right; prefix with `left` \
   to rewrite right to left; an optional pattern restricts the \
   rewritten occurrences.",
  "rewrite ${1:eq}";

  "set", "define a local abbreviation",
  "`set x \xe2\x89\x94 t` extends the current context with \
   `x \xe2\x89\x94 t`.",
  "set ${1:x} \xe2\x89\x94 ${2:term}";

  "simplify", "simplify the goal",
  "Normalizes the focused goal with respect to β-reduction and \
   rewriting rules; `simplify rule off` uses β-reduction only; \
   `simplify f` unfolds the definition of `f` or applies its rules.",
  "simplify";

  "solve", "simplify unification goals",
  "Simplifies unification goals as much as possible.",
  "solve";

  "symmetry", "swap sides of an equation",
  "Replaces a goal of the form `P (t = u)` by `P (u = t)`.",
  "symmetry";

  "try", "try a tactic; never fails",
  "`try t` applies `t`; if `t` fails, the goal is left unchanged.",
  "try ${1:tac}";

  "why3", "dispatch to an external prover",
  "Calls an external prover through the Why3 platform to solve the \
   current goal; `why3 \"prover\"` selects a specific prover (default \
   Alt-Ergo, or the one set with the `prover` command).",
  "why3";
]

(** Documentation of a tactic keyword, if [name] is one. *)
let tactic_doc (name : string) : string option =
  List.find_map
    (fun (tn, _, doc, _) -> if tn = name then Some doc else None)
    tactic_completions

let is_tactic_name n = tactic_doc n <> None

(** Command keywords and symbol modifiers: offered as completions
    where the grammar accepts them (anywhere outside proofs when the
    prefix does not parse) and documented on hover anywhere in a
    document. Same [(name, detail, doc, snippet)] entries as
    [tactic_completions]; docs sourced from [doc/commands.rst]. *)
let keyword_completions : (string * string * string * string) list = [
  "symbol", "declare or define a symbol",
  "Declares or defines a symbol. Syntax: \
   `modifiers symbol id params [: type] [≔ [term]] [begin proof end] \
   ;`. Without `≔` it is a declaration (axiom); with `≔` a \
   definition or theorem.",
  "symbol ${1:id} : ${2:type};";

  "inductive", "define an inductive type",
  "Defines inductive types with their constructors, and generates \
   their induction principles `ind_<name>` and rules (requires the \
   `Prop` and `P` builtins). Mutually defined types are linked with \
   `with`.",
  "inductive ${1:id} : ${2:type} \xe2\x89\x94\n| ${3:c} : $1;";

  "rule", "declare a rewriting rule",
  "Declares rewriting rules for definable symbols, e.g. \
   `rule add zero $n ↪ $n;`. `$`-prefixed identifiers are pattern \
   variables. Rules should form a confluent and terminating system; \
   chain several with `with`.",
  "rule ${1:lhs} \xe2\x86\xaa ${2:rhs};";

  "with", "chain rules or inductive types",
  "Chains additional rewriting rules (`rule … with …`) or links \
   mutually defined inductive types.",
  "with ${1:lhs} \xe2\x86\xaa ${2:rhs}";

  "require", "import modules",
  "Imports the non-private symbols, rules and builtins of other \
   modules, usable qualified (`Stdlib.Bool.true`); `require open` \
   also puts them in scope; `require … as …` gives the module an \
   alias.",
  (* [open], [private] and module paths complete after the keyword,
     so the snippet presumes none of the alternatives. *)
  "require $0;";

  "open", "bring module symbols into scope",
  "Puts into scope the symbols of previously required modules. \
   Non-private `open`s are transitively inherited.",
  "open $0;";

  "builtin", "map a builtin name to a symbol",
  "Maps an internal string literal to a user symbol, e.g. \
   `builtin \"P\" ≔ …;` — required by some commands, tactics and \
   notations.",
  "builtin \"${1:name}\" \xe2\x89\x94 ${2:id};";

  "notation", "set a symbol's notation",
  "Sets the notation of a symbol: `infix`/`prefix`/`postfix` with an \
   optional priority, or `quantifier`.",
  (* The notation kind is completed contextually after the id, so
     the snippet does not presume one. *)
  "notation ${1:id} $0";

  "opaque", "never unfold the definition",
  "The symbol is never reduced to its definition (typical for \
   theorems). As a command, `opaque x;` makes a previously defined \
   symbol opaque.",
  "opaque";

  "unif_rule", "declare a unification rule",
  "Declares a unification rule `t ≡ u ↪ [t₁ ≡ u₁; …]`, tried by the \
   unification engine when a problem cannot be solved by the default \
   algorithm.",
  "unif_rule";

  "coerce_rule", "declare a coercion rule",
  "Declares a coercion rule, used to automatically insert coercions \
   between types.",
  "coerce_rule";

  "begin", "start a proof script",
  "Starts a proof script solving the pending goals with tactics; \
   close it with `end`, `admitted` or `abort`.",
  "begin\n  $0\nend;";

  "constant", "modifier: no rules or definition",
  "Property modifier: no rewriting rule or definition can ever be \
   given to the symbol.",
  "constant";

  "injective", "modifier: may be considered injective",
  "Property modifier: the symbol may be considered injective, i.e. \
   if `f t₁ … tₙ ≡ f u₁ … uₙ` then `t₁ ≡ u₁`, …, `tₙ ≡ uₙ`. The \
   verification is left to the user.",
  "injective";

  "commutative", "modifier: add commutativity",
  "Property modifier: adds the equation `f t u ≡ f u t` to the \
   conversion.",
  "commutative";

  "associative", "modifier: add associativity",
  "Property modifier: adds the equation `f (f t u) v ≡ f t (f u v)` \
   to the conversion (in conjunction with `commutative` only); \
   `left`/`right` selects the canonical form.",
  "associative";

  "private", "modifier: not visible outside the module",
  "Exposition modifier: the symbol cannot be used outside the module \
   where it is defined.",
  "private";

  "protected", "modifier: only rule LHS outside the module",
  "Exposition modifier: outside its module, the symbol can only be \
   used in the left-hand side of rewriting rules.",
  "protected";

  "sequential", "modifier: try rules in declaration order",
  "Matching strategy modifier: apply the symbol's rules in \
   declaration order instead of the default order-independent \
   strategy. Warning: this can break important properties.",
  "sequential";
]

(** Proof-closing keywords, offered as completions inside proofs. *)
let proof_end_completions : (string * string * string * string) list = [
  "end", "close a finished proof",
  "Ends a proof script once all goals are solved.",
  "end;";

  "admitted", "accept the remaining goals as axioms",
  "Ends a proof accepting the remaining goals as axioms.",
  "admitted;";

  "abort", "abort the proof",
  "Aborts the proof: the symbol is not added to the environment.",
  "abort;";
]

(** Queries, valid both as commands and as tactics ([P_tac_query]):
    offered as completions in both contexts and documented on hover.
    Docs sourced from [doc/queries.rst]. *)
let query_completions : (string * string * string * string) list = [
  "assert", "check a typing or a conversion",
  "`assert x₁ … xₙ ⊢ t : A;` checks that `t` has type `A`; \
   `assert x₁ … xₙ ⊢ t ≡ u;` checks that `t` and `u` are \
   convertible. Fails if the judgment does not hold.",
  "assert \xe2\x8a\xa2 ${1:term} : ${2:type}";

  "assertnot", "check that a typing or conversion fails",
  "Like `assert`, but succeeds when the typing or conversion \
   judgment does NOT hold.",
  "assertnot \xe2\x8a\xa2 ${1:term} : ${2:type}";

  "compute", "normalize a term",
  "Computes the normal form of a term.",
  "compute ${1:term}";

  "debug", "toggle debug flags",
  "Activates (`+`) or deactivates (`-`) debug modes, each named by \
   one character, e.g. `debug +ts;`. Without argument, lists the \
   available flags.",
  "debug +${1:flags}";

  "flag", "set an option flag on/off",
  "Sets a flag `on` or `off`, e.g. `flag \"print_implicits\" on;`. \
   Most flags modify printing; only `\"eta_equality\"` changes the \
   rewrite engine. Without argument, lists the available flags.",
  "flag \"${1:name}\" ${2:on}";

  "print", "print a symbol or the goals",
  "With a symbol identifier, displays information (type, notation, \
   rules, …) about that symbol; with `unif_rule` or `coerce_rule`, \
   the corresponding rules; without argument, the current goals.",
  "print";

  "proofterm", "print the current proof term",
  "Outputs the current proof term.",
  "proofterm";

  "prover", "select the why3 prover",
  "Changes the prover used by the `why3` tactic (default \
   *Alt-Ergo*), e.g. `prover \"Eprover\";`.",
  "prover \"${1:name}\"";

  "prover_timeout", "set the why3 timeout",
  "Changes the timeout (in seconds) of the `why3` tactic; initially \
   2s.",
  "prover_timeout ${1:seconds}";

  "search", "query the search index",
  "Runs a query (see the query language documentation) against the \
   index of the current file and its requirements, e.g. \
   `search spine >= (nat → nat);`.",
  "search ${1:query}";

  "type", "print the type of a term",
  "Displays the type of a term in the current context.",
  "type ${1:term}";

  "verbose", "set the verbosity level",
  "Takes a non-negative integer: the higher, the more details are \
   printed. Initially 1.",
  "verbose ${1:level}";
]

(* Argument keywords (notation kinds, sides, switches, [as]) are
   deliberately absent here: no hover docs for them, they are only
   described in their completion items. *)
let keyword_doc (name : string) : string option =
  List.find_map
    (fun (kn, _, doc, _) -> if kn = name then Some doc else None)
    (keyword_completions @ proof_end_completions @ query_completions)

(** Hypotheses visible at the cursor inside a proof. Returns the
    focused goal's [(name, type_string)] list, or [[]] when no goal
    is active at that position. Goal printing prefixes hypothesis
    types with ": "; strip it so consumers get the bare type, in line
    with symbol hovers. *)
let hyps_at_cursor (doc : Lp_doc.t) line character : (string * string) list =
  match get_context_node doc line character with
  | None -> []
  | Some n ->
    let strip_type t =
      let t = String.trim t in
      if String.length t > 0 && t.[0] = ':' then
        String.trim (String.sub t 1 (String.length t - 1))
      else t
    in
    let hyps_of goals =
      match goals with
      | (hyps, _) :: _ ->
        List.map (fun (hn, ht) -> (hn, strip_type ht)) hyps
      | [] -> []
    in
    (* Goal snapshots record the state after each tactic, anchored at
       the tactic's keyword, so the snapshot at the cursor belongs to
       the tactic the cursor is in. But a tactic's arguments are
       elaborated in the state *before* it runs: the post-state may
       focus a different goal when the tactic closes the current one
       (dropping its local hypotheses), or no goal at all when it ends
       the proof. So resolve names in the pre-state — the snapshot
       preceding the anchor, not merely the start of the line, which
       skips too far back when several tactics share a line — and keep
       the post-state for names the tactic itself binds, e.g. the [x]
       of [assume x]. *)
    (match closest_before (line + 1, character) n.Lp_doc.goals with
     | None -> []
     | Some (post_goals, gpos) ->
       let post = hyps_of post_goals in
       let pre =
         match gpos with
         | Some Pos.{start_line; start_col; _} ->
           (match
              closest_before (start_line, start_col - 1) n.Lp_doc.goals
            with
            | Some (goals, _) -> hyps_of goals
            | None -> [])
         | None -> []
       in
       pre @ List.filter (fun (hn, _) -> not (List.mem_assoc hn pre)) post)

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
    (* Ghost symbols (internal symbols used e.g. for unification rules
       and string literals) have no user-facing definition site one
       could jump to. *)
    let definfo_of_sym (s : Term.sym) : J.t =
      if s.Term.sym_path = Sign.Ghost.path then `Null
      else
        let file =
          Library.(file_of_path s.Term.sym_path ^ lp_src_extension) in
        let pos = Option.get (Pos.file_start file) s.Term.sym_pos in
        mk_definfo file pos
    in
    (* Fallback when the identifier RangeMap has no resolvable entry
       at the cursor: the module paths of require/open commands (jump
       to the start of that module's file), then the raw token under
       the cursor against the in-scope symbol table — the latter also
       covers regions the checker never reached (mid-edit text, code
       past a parse error). *)
    let def_fallback () =
      match RangeMap.find pt doc.path_map with
      | Some (_, path) ->
        let file = Library.(file_of_path path ^ lp_src_extension) in
        mk_definfo file (Pos.file_start file)
      | None ->
        match token_at_pos doc ln pos with
        | None ->
          LIO.log_error "do_definition" "no symbol at point"; `Null
        | Some tok ->
          match Extra.StrMap.find_opt tok (Pure.get_symbols ss) with
          | Some s -> definfo_of_sym s
          | None ->
            LIO.log_error "do_definition" "no symbol at point"; `Null
    in
    let sym_info =
      match get_symbol pt doc.map with
      | Some (qid, _) ->
        LIO.log_error "do_definition" (snd qid);
        (match Pure.find_sym ss qid with
         | Some s -> definfo_of_sym s
         | None when fst qid = [] -> def_fallback ()
         | None -> `Null)
      | None -> def_fallback ()
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
    (* Not just [restore_time]: hover prints types, and the printer's
       signature state ([Print.sig_state]) is a plain ref that time
       restoration does not cover — without this, types would render
       with whichever document's notations were installed last. *)
    Pure.set_print_state ss;

    let send_type_hover ?range sym =
      let sym_type = Format.asprintf "%a" Core.Print.sym_type sym in
      let fields = ["contents", `String sym_type] in
      let fields = match range with
        | Some r -> fields @ ["range", LSP.mk_range_of_interval r]
        | None -> fields
      in
      LIO.send_json ofmt (LSP.mk_reply ~id ~result:(`Assoc fields))
    in
    let send_contents s =
      LIO.send_json ofmt
        (LSP.mk_reply ~id ~result:(`Assoc ["contents", `String s]))
    in
    (* Token-based fallback, tried when the identifier RangeMap has no
       resolvable entry at the cursor: tactic keywords (inside proofs)
       and hypotheses of the focused goal, then command keywords and
       modifiers, then in-scope symbols. Text-based, so it also covers
       regions the checker never reached (mid-edit text, code past a
       parse error). *)
    let hover_fallback () =
      match token_at_pos doc ln pos with
      | None -> send_null ()
      | Some tok ->
        let in_proof = in_proof_at doc ln pos in
        match (if in_proof then tactic_doc tok else None) with
        | Some d -> send_contents d
        | None ->
          match
            (if in_proof then
               List.assoc_opt tok (hyps_at_cursor doc ln pos)
             else None)
          with
          | Some htype -> send_contents htype
          | None ->
            match keyword_doc tok with
            | Some d -> send_contents d
            | None ->
              match Extra.StrMap.find_opt tok (Pure.get_symbols ss) with
              | Some sym when sym.Term.sym_path <> Sign.Ghost.path ->
                send_type_hover sym
              | _ -> send_null ()
    in
    match get_symbol pt doc.map with
    | Some (qid, range) ->
      (match Pure.find_sym ss qid with
       | Some sym -> send_type_hover ~range sym
       (* Unresolvable unqualified identifier: typically a proof-local
          name (hypothesis) — try the fallback chain. *)
       | None when fst qid = [] -> hover_fallback ()
       | None -> send_null ())
    | None -> hover_fallback ()
  with e ->
    LIO.log_error "hover_symInfo" (Printexc.to_string e);
    send_null ()

(* --- Completion ------------------------------------------------------- *)

(** Completion items for a keyword table ([tactic_completions],
    [keyword_completions], [proof_end_completions]): docs as markdown
    and snippet insertions when the client supports them.
    [sort_prefix] orders keyword groups relative to each other and to
    the hypotheses group ("1"). *)
let mk_keyword_items (sort_prefix : string)
    (entries : (string * string * string * string) list) : J.t list =
  List.map (fun (name, detail, doc, snippet) ->
    let doc_field =
      if !markdown_completion_docs then
        `Assoc [ "kind", `String "markdown"
               ; "value", `String doc ]
      else `String doc
    in
    let base = [
      "label", `String name;
      "kind",  `Int 14;                 (* Keyword *)
      "detail", `String detail;
      "documentation", doc_field;
      "sortText", `String (sort_prefix ^ name);
    ] in
    `Assoc (
      if !snippet_support then
        base @
        [ "insertText", `String snippet
        ; "insertTextFormat", `Int 2 ]  (* Snippet *)
      else base)
  ) entries

(* Argument keywords of the [notation] command. *)
let notation_arg_completions : (string * string * string * string) list = [
  "infix", "infix notation",
  "`notation f infix [left|right] p;` sets an infix notation for \
   `f` with priority `p`, optionally left/right associative.",
  "infix ${1:priority}";

  "prefix", "prefix notation",
  "`notation f prefix p;` sets a prefix notation for `f` with \
   priority `p`.",
  "prefix ${1:priority}";

  "postfix", "postfix notation",
  "`notation f postfix p;` sets a postfix notation for `f` with \
   priority `p`.",
  "postfix ${1:priority}";

  "quantifier", "binder notation",
  "`notation f quantifier;` allows writing `` `f x, t`` for \
   `f (λ x, t)`.",
  "quantifier";
]

(* Associativity sides, after [associative] or [infix]. *)
let assoc_side_completions : (string * string * string * string) list = [
  "left", "left associative", "Selects left associativity.", "left";
  "right", "right associative", "Selects right associativity.", "right";
]

(* The switch argument of [flag "..."]. *)
let switch_completions : (string * string * string * string) list = [
  "on", "enable the flag", "Turns the flag on.", "on";
  "off", "disable the flag", "Turns the flag off.", "off";
]

(* Keywords only valid as arguments of other commands, never offered
   without grammar support. *)
let arg_keyword_completions : (string * string * string * string) list = [
  "as", "alias for the required module",
  "`require M as N;` gives the module `M` the alias `N`, usable in \
   qualified names (`N.symb`).",
  "as ${1:alias}";
]

(* Names of the registered boolean flags, offered inside the string
   argument of [flag]. *)
let flag_name_items () : J.t list =
  Extra.StrMap.fold
    (fun name _ acc -> `Assoc ["label", `String name] :: acc)
    Stdlib.(!Console.boolean_flags) []

(* Names under which a follow-set token may appear in the keyword
   tables. Tokens without a keyword rendering (identifiers, literals,
   punctuation) map to a phrase no table entry uses, and to nothing
   in the end. *)
let token_names (tk : Parsing.LpLexer.token) : string list =
  match tk with
  | Parsing.LpLexer.ASSERT _ -> ["assert"; "assertnot"]
  | Parsing.LpLexer.SIDE _ -> ["left"; "right"]
  | Parsing.LpLexer.SWITCH _ -> ["on"; "off"]
  | _ -> [Parsing.LpParser.string_of_token tk]

(* The keyword tables, with the rank their items keep relative to
   each other when offered from a follow set: queries and proof
   enders sort after the keywords specific to the context. *)
let follow_tables : (string * (string * string * string * string) list) list =
  [ "0", tactic_completions;
    "0", keyword_completions;
    "0", notation_arg_completions;
    "0", assoc_side_completions;
    "0", switch_completions;
    "0", arg_keyword_completions;
    "2", query_completions;
    "2", proof_end_completions ]

(** Completion items for the keywords of a parser follow set: the
    grammar decides membership, the tables provide the docs and
    snippets. [exclude] drops named keywords (already-typed
    modifiers). *)
let follow_keyword_items ?(exclude : string list = [])
    (follow : Parsing.LpLexer.token list) : J.t list =
  let names =
    List.filter (fun n -> not (List.mem n exclude))
      (List.concat_map token_names follow) in
  List.concat_map (fun (rank, table) ->
    mk_keyword_items rank
      (List.filter (fun (n, _, _, _) -> List.mem n names) table))
    follow_tables

(* Whether the grammar accepts a qualified identifier at a position
   with this follow set: a symbol reference (term or identifier
   position) or a module path (after [require]/[open]). Binder
   positions (a fresh name after [as], [assume], [symbol], …) only
   accept unqualified identifiers, so they don't trigger symbol
   completion. *)
let follow_accepts_qid (follow : Parsing.LpLexer.token list) : bool =
  List.exists
    (function
      | Parsing.LpLexer.QID _ | Parsing.LpLexer.QID_EXPL _ -> true
      | _ -> false)
    follow

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
      let reply items =
        LIO.send_json ofmt (LSP.mk_reply ~id ~result:(`Assoc [
          "isIncomplete", `Bool false; "items", `List items])) in
      (* A "."-triggered popup only makes sense in the contexts that
         understand dots; stay quiet in the others. *)
      let dot_triggered =
        match json_path (`Assoc params) ["context"; "triggerKind"] with
        | Some (`Int 2) -> true
        | _ -> false
      in
      let ctx = completion_context doc line character in
      match ctx with
      | Ctx_require (partial, start_col) ->
        (* Module paths, plus the keywords the grammar still accepts
           at the cursor ([open], [private], [as], …). No paths where
           the grammar refuses one (after [require private]); an
           empty follow set (a partial path ending in ".") cannot
           tell, so it offers them. *)
        let follow = follow_at doc line character in
        let path_items =
          if follow = [] || follow_accepts_qid follow then
            mk_module_path_items ~line ~start_col
              ~cursor_col:character partial
          else [] in
        reply (path_items @ follow_keyword_items follow)
      | Ctx_qualified (mpath, _) ->
        reply (mk_qualified_items ss uri mpath)
      | Ctx_flag_name -> reply (flag_name_items ())
      | (Ctx_default | Ctx_tactic_arg) when dot_triggered -> reply []
      | Ctx_default | Ctx_tactic_arg ->
        let follow = follow_at doc line character in
        let in_proof = in_proof_at doc line character in
        (* Symbols, where the grammar accepts a symbol reference (a
           term or identifier position). An unparseable prefix (a
           broken edit earlier in the file) yields no follow set;
           offer them regardless then. No [kind]: the LSP completion
           kinds don't match lambdapi's notions, so we don't force a
           classification. `detail` is filled in on
           [completionItem/resolve]; [data] carries what resolve
           needs to find the symbol again. *)
        let symbol_items =
          if follow <> [] && not (follow_accepts_qid follow) then []
          else
            Extra.StrMap.fold (fun name s acc ->
              (* Ghost symbols (internal, e.g. for unification rules)
                 are not part of the user-facing scope. Inside a proof,
                 tactic keywords shadow symbols of the same name in the
                 completion list: the user almost certainly means the
                 tactic. *)
              if s.Term.sym_path = Sign.Ghost.path
              || (in_proof && is_tactic_name name) then acc
              else
                `Assoc [
                  "label", `String name;
                  "data",  `Assoc [ "kind", `String "symbol"
                                  ; "uri",  `String uri ];
                ] :: acc
            ) (Pure.get_symbols ss) [] in
        (* Keywords the grammar accepts at the cursor. Without a
           follow set, fall back to context-blind tables: tactic
           keywords and proof enders inside proofs, command keywords
           outside, queries in both. *)
        let typed_modifiers =
          match line_prefix doc line character with
          | Some p ->
            List.filter (fun w -> List.mem w modifier_words)
              (fst (words_and_partial p))
          | None -> [] in
        let keyword_items =
          match follow with
          | _ :: _ -> follow_keyword_items ~exclude:typed_modifiers follow
          | [] ->
            match ctx with
            (* The argument of a tactic is a term position: keywords
               are not valid there. *)
            | Ctx_tactic_arg -> []
            | _ when in_proof ->
              mk_keyword_items "0" tactic_completions
              @ mk_keyword_items "2" (query_completions
                                      @ proof_end_completions)
            | _ ->
              mk_keyword_items "0" keyword_completions
              @ mk_keyword_items "2" query_completions in
        (* Hypotheses of the focused goal, ranked before the symbols
           in the argument position of a hypothesis-taking tactic. *)
        let hyp_rank =
          match ctx with Ctx_tactic_arg -> "0" | _ -> "1" in
        let hyp_items =
          if not in_proof then [] else
            List.map (fun (hname, htype) ->
              `Assoc [
                "label", `String hname;
                "kind",  `Int 6;                  (* Variable *)
                "detail", `String htype;
                "sortText", `String (hyp_rank ^ hname);
              ]
            ) (hyps_at_cursor doc line character) in
        let result = `Assoc [
          "isIncomplete", `Bool false;
          "items", `List (symbol_items @ keyword_items @ hyp_items);
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
  (* Re-find the completed symbol via [find] (with the document's
     print state installed) and send the item back with its
     pretty-printed type as [detail]. *)
  let resolve_with uri (find : Pure.state -> Term.sym option) =
    match Hashtbl.find_opt completed_table uri with
    | None -> echo ()
    | Some doc ->
      match doc.Lp_doc.final with
      | None -> echo ()
      | Some ss ->
        Pure.set_print_state ss;
        match find ss with
        | None -> echo ()
        | Some sym ->
          let type_str =
            Format.asprintf "%a" Core.Print.sym_type sym in
          let fields =
            ("detail", `String type_str) ::
            List.remove_assoc "detail" params in
          LIO.send_json ofmt (LSP.mk_reply ~id ~result:(`Assoc fields))
  in
  match List.assoc_opt "data" params with
  | Some (`Assoc data) ->
    let uri = try string_field "uri" data with _ -> "" in
    let label = try string_field "label" params with _ -> "" in
    (match List.assoc_opt "kind" data with
     | Some (`String "symbol") ->
       (* Items are generated from the in-scope symbol map, keyed by
          the label; resolve the highlighted item from the same map. *)
       resolve_with uri (fun ss ->
           Extra.StrMap.find_opt label (Pure.get_symbols ss))
     | Some (`String "qualified") ->
       let path =
         try String.split_on_char '.' (string_field "path" data)
         with _ -> [] in
       resolve_with uri (fun _ss ->
           match Path.Map.find_opt path (Timed.(!) Sign.loaded) with
           | None -> None
           | Some sign ->
             Extra.StrMap.find_opt label
               (Timed.(!) sign.Sign.sign_symbols))
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
