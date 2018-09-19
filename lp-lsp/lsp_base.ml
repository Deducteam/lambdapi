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

(* Whether to send extended lsp messages *)
let std_protocol = ref true

module J = Yojson.Basic

let mk_extra l = if !std_protocol then [] else l

(* Ad-hoc parsing for file:///foo... *)
let parse_uri str =
  let l = String.length str - 7 in
  String.(sub str 7 l)

let mk_reply ~id ~result = `Assoc [ "jsonrpc", `String "2.0"; "id",     `Int id;   "result", result ]
let mk_event m p   = `Assoc [ "jsonrpc", `String "2.0"; "method", `String m; "params", `Assoc p ]

let json_of_goal g =
  let pr_hyp (s,(_,t)) =
    `Assoc ["hname", `String s;
            "htype", `String (Format.asprintf "%a" Print.pp_term (Bindlib.unbox t))] in
  let open Proofs in
  let j_env = List.map pr_hyp g.g_hyps in
  `Assoc [
    "gid", `Int g.g_meta.meta_key
  ; "hyps", `List j_env
  ; "type", `String (Format.asprintf "%a" Print.pp_term g.g_type)]

let json_of_thm thm =
  let open Proofs in
  match thm with
  | None ->
    `Null
  | Some thm ->
    `Assoc [
      "goals", `List List.(map json_of_goal thm.t_goals)
    ]

let mk_range (p : Pos.pos) : J.json =
  let open Pos in
  let line1 = Input.line_num p.start_buf in
  let line2 = Input.line_num p.end_buf   in
  let col1  = Input.utf8_col_num p.start_buf p.start_pos in
  let col2  = Input.utf8_col_num p.end_buf   p.end_pos   in
  `Assoc ["start", `Assoc ["line", `Int (line1 - 1); "character", `Int col1];
          "end",   `Assoc ["line", `Int (line2 - 1); "character", `Int col2]]

let mk_diagnostic ((p : Pos.pos), (lvl : int), (msg : string), (thm : Proofs.theorem option)) : J.json =
  let goal = json_of_thm thm in
  let range = mk_range p in
  `Assoc (mk_extra ["goal_info", goal] @
          ["range", range;
           "severity", `Int lvl;
           "message",  `String msg;
          ])

let mk_diagnostics ~uri ~version ld : J.json =
  let extra = mk_extra ["version", `Int version] in
  mk_event "textDocument/publishDiagnostics" @@
    extra @
    ["uri", `String uri;
     "diagnostics", `List List.(map mk_diagnostic ld)]
