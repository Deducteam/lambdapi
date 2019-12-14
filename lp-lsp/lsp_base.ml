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

(* Whether to send extended lsp messages *)
let std_protocol = ref true

module J = Yojson.Basic

let mk_extra l = if !std_protocol then [] else l

(* Ad-hoc parsing for file:///foo... *)
let _parse_uri str =
  let l = String.length str - 7 in
  String.(sub str 7 l)

let mk_reply ~id ~result = `Assoc [ "jsonrpc", `String "2.0"; "id",     `Int id;   "result", result ]
let mk_event m p   = `Assoc [ "jsonrpc", `String "2.0"; "method", `String m; "params", `Assoc p ]

let mk_range (p : Pos.pos) : J.t =
  let open Pacomb.Pos in
  let {start = {line=line1; col=col1; _}
      ;end_  = {line=line2; col=col2; _}} = p
  in
  `Assoc ["start", `Assoc ["line", `Int (line1 - 1); "character", `Int col1];
          "end",   `Assoc ["line", `Int (line2 - 1); "character", `Int col2]]

let json_of_goal g =
  let pr_hyp (s,(_,t)) =
    `Assoc ["hname", `String s;
            "htype", `String (Format.asprintf "%a" Print.pp_term (Bindlib.unbox t))] in
  let open Proof in
  let g_meta = Goal.get_meta g in
  let hyp, typ = Goal.get_type g in
  let j_env = List.map pr_hyp hyp in
  `Assoc [
    "gid", `Int g_meta.meta_key
  ; "hyps", `List j_env
  ; "type", `String (Format.asprintf "%a" Print.pp_term typ)]

let json_of_goals goals =
  match goals with
  | None ->
    `Null
  | Some goals ->
    `Assoc [
      "goals", `List List.(map json_of_goal goals)
    ]

let mk_diagnostic ((p : Pos.pos), (lvl : int), (msg : string), (goals : _ option)) : J.t =
  let goals = json_of_goals goals in
  let range = mk_range p in
  `Assoc (mk_extra ["goal_info", goals] @
          ["range", range;
           "severity", `Int lvl;
           "message",  `String msg;
          ])

let mk_diagnostics ~uri ~version ld : J.t =
  let extra = mk_extra ["version", `Int version] in
  mk_event "textDocument/publishDiagnostics" @@
    extra @
    ["uri", `String uri;
     "diagnostics", `List List.(map mk_diagnostic ld)]
