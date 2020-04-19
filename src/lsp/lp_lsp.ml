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

open Core

module F = Format
module J = Yojson.Basic
module U = Yojson.Basic.Util

(* OCaml 4.04 compat *)
module Hashtbl = struct
  include Hashtbl
  let find_opt n d = try Some Hashtbl.(find n d) with | Not_found -> None
end

module List = struct
  include List
  let assoc_opt n d = try Some List.(assoc n d) with | Not_found -> None
  let find_opt f l = try Some List.(find f l) with | Not_found -> None
end

module StrMap = struct
  include Extra.StrMap
  let find_opt key map =
    try Some (find key map)
    with | Not_found -> None
end

module Option = struct
  let _iter f x = match x with | None -> () | Some x -> f x
  let _map f x = match x with | None -> None | Some x -> Some (f x)
end

let    int_field name dict = U.to_int    List.(assoc name dict)
let   dict_field name dict = U.to_assoc  List.(assoc name dict)
let   list_field name dict = U.to_list   List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

(* Conditionals *)
let option_empty x = match x with | None -> true | Some _ -> false
let option_cata f x d = match x with | None -> d | Some x -> f x
let option_default x d = match x with | None -> d | Some x -> x

let oint_field  name dict = option_cata U.to_int List.(assoc_opt name dict) 0
let odict_field name dict =
  option_default U.(to_option to_assoc
                      (option_default List.(assoc_opt name dict) `Null)) []

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
  let open Terms in
  let open Timed in
  let is_undef =
    option_empty !(tm.sym_def) && List.length !(tm.sym_rules) = 0 in
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
        let open Terms in
        (* LIO.log_error "sym"
         ( s.sym_name ^ " | "
         ^ Format.asprintf "%a" pp_term !(s.sym_type)); *)
        option_cata
          (fun p -> mk_syminfo file
                      (s.sym_name, s.sym_path, kind_of_type s, p) :: l) p l)
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
  | Some loc ->
      let { Pos.start_line ; start_col ; end_line ; end_col ; _ } =
        Lazy.force loc in
    start_line - 1 < line && line < end_line - 1 ||
    (start_line - 1 = line && start_col <= pos) ||
    (end_line - 1 = line && pos <= end_col)

let get_goals ~doc ~line ~pos =
  let open Lp_doc in
  let node =
    List.find_opt (fun { ast; _ } ->
        let loc = Pure.Command.get_pos ast in
        let res = in_range ?loc (line,pos) in
        let ls = Format.asprintf "%B l:%d p:%d / %a "
                   res line pos Pos.print loc in
        LIO.log_error "get_goals" ("call: "^ls);
        res
      ) doc.Lp_doc.nodes in
  let goalsList = match node with
    | None -> []
    | Some n -> n.goals in
  let goals =
    match List.find_opt (fun (_, loc) -> in_range ?loc (line,pos)) goalsList
    with
    | None -> None
    | Some (v,_) -> Some v in
  goals

let do_goals ofmt ~id params =
  let uri, line, pos = get_docTextPosition params in
  let doc = Hashtbl.find completed_table uri in
  let goals = get_goals ~doc ~line ~pos in
  let result = LSP.json_of_goals goals in
  let msg = LSP.mk_reply ~id ~result in
  LIO.send_json ofmt msg

let msg_fail hdr msg =
  LIO.log_error hdr msg;
  failwith msg

(** [get_token line pos] tries to extract the corresponding token from
   [line] for column [pos] ; this is used in go to definition, type on
   hover, etc... The function is a bit complex due to the use of
   Unicode chars in the Lambdapi code, it could surely be improved. *)
let get_token line pos =
  let regexp = Str.regexp "[^a-zA-Z0-9_]" in
  let res_split = Str.full_split regexp line in
  let count = 0 in
  let rec iter_tokens count tokens pos =
    match tokens with
    | [] -> ""
    | t::ts -> match t with
      | Str.Text txt ->
        let new_count = count + String.length txt in
        if new_count >= pos
        then txt
        else iter_tokens new_count ts pos
      | Str.Delim s ->
        if String.equal s "\226"
        then
          let sym_table = ["\226\135\146"; "\226\134\146"; "\226\136\128"] in
          let find_symb ts sym_table =
            match ts with
            | [] ->
              msg_fail "get_token" "unicode symbol not in table"
            | _::[] ->
              msg_fail "get_token" "not enough chars"
            | a::b::tl ->
              match a,b with
              | Str.Delim c, Str.Delim d ->
                if List.mem ("\226"^c^d) sym_table
                then
                  let new_count = count + 1 in
                  iter_tokens new_count tl pos
                else
                  let new_count = count + 1 in
                  iter_tokens new_count ts pos
              | _, _ ->
                msg_fail "get_token" "expected Delim in split"
          in find_symb ts sym_table
        else
          let new_count = (count + 1) in
          iter_tokens new_count ts pos
  in iter_tokens count res_split pos

let get_symbol text l pos =
  let lines = String.split_on_char '\n' text in
  let line = List.nth lines l in
  get_token line pos

let do_definition ofmt ~id params =
  let file, _, doc = grab_doc params in
  let line, pos = get_textPosition params in
  let sym_target = get_symbol doc.text line pos in
  LIO.log_error "definition" sym_target;

  let sym = Pure.get_symbols doc.final in
  let map_pp : string =
    Extra.StrMap.bindings sym
    |> List.map (fun (key, (sym,pos)) ->
           Format.asprintf "{%s} / %s: @[%a@]"
             key sym.Terms.sym_name Pos.print pos)
    |> String.concat "\n"
  in
  LIO.log_error "symbol map" map_pp;

  let sym_info =
    match StrMap.find_opt sym_target sym with
    | None
    | Some (_, None) -> `Null
    | Some (_, Some pos) -> mk_definfo file pos
  in
  let msg = LSP.mk_reply ~id ~result:sym_info in
  LIO.send_json ofmt msg

let hover_symInfo ofmt ~id params =
  let _, _, doc = grab_doc params in
  let line, pos = get_textPosition params in
  let sym_target = get_symbol doc.text line pos in
  let sym = Pure.get_symbols doc.final in
  let map_pp : string =
    Extra.StrMap.bindings sym
    |> List.map (fun (key, (sym,pos)) ->
           Format.asprintf "{%s} / %s: @[%a@]"
             key sym.Terms.sym_name Pos.print pos)
    |> String.concat "\n"
  in
  LIO.log_error "symbol map" map_pp;

  let sym_found = let open Timed in let open Terms in
    match StrMap.find_opt sym_target sym with
    | None ->
      msg_fail "hover" "sym not found"
    | Some (_, None) ->
      msg_fail "hover" "sym not found"
    | Some (sym, Some _) ->
      !(sym.sym_type)
  in let sym_type : string =
    Format.asprintf "%a" Print.pp_term sym_found  in
  let result = `Assoc [ "contents", `String sym_type] in
  let msg = LSP.mk_reply ~id ~result in
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
  | "workspace/didChangeWatchedFiles" ->
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

let default_log_file : string = "/tmp/lambdapi_lsp_log.txt"
