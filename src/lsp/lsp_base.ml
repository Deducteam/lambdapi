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

open Common

(* Whether to send extended lsp messages *)
let std_protocol = ref true

module J = Yojson.Basic

let mk_extra l = if !std_protocol then [] else l

(* Ad-hoc parsing for file:///foo... *)
let _parse_uri str =
  let l = String.length str - 7 in
  String.(sub str 7 l)

let mk_reply ~id ~result =
  `Assoc [ "jsonrpc", `String "2.0"; "id",     `Int id;   "result", result ]

let mk_event m p   =
  `Assoc [ "jsonrpc", `String "2.0"; "method", `String m; "params", `Assoc p ]

let mk_range (p : Pos.pos) : J.t =
  let open Pos in
  let {start_line=line1; start_col=col1; end_line=line2; end_col=col2; _} =
    p
  in
  `Assoc ["start", `Assoc ["line", `Int (line1 - 1); "character", `Int col1];
          "end",   `Assoc ["line", `Int (line2 - 1); "character", `Int col2]]

let json_of_goal (hyps, concl) =
  let json_of_hyp (s,t) = `Assoc ["hname", `String s; "htype", `String t] in
  match concl with
  | Pure.Typ (meta, typ) ->
    `Assoc [
      "typeofgoal", `String "Typ"
    ; "gid", `String meta
    ; "hyps", `List (List.map json_of_hyp hyps)
    ; "type", `String typ]
  | Pure.Unif (t,u) ->
    `Assoc [
      "typeofgoal", `String "Unif"
    ; "hyps", `List (List.map json_of_hyp hyps)
    ; "constr", `String (t ^ " ≡ " ^ u)]

let json_of_goals ?logs goals =
  let logs = match logs with None -> "" | Some s -> s in
  match goals with
  | None ->
    `Assoc [
      "logs", `String logs
    ]
  | Some goals ->
    `Assoc [
      "goals", `List List.(map json_of_goal goals);
      "logs" , `String logs
    ]

let mk_diagnostic
      ((p : Pos.pos), (lvl : int), (msg : string), (goals : _ option)) : J.t =
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
