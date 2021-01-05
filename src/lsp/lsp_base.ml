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

let json_of_goal g =
  let pr_hyp (s,(_,t,_)) =
    let t = Format.asprintf "%a" Print.pp_term (Bindlib.unbox t) in
    `Assoc ["hname", `String s; "htype", `String t]
  in
  let open Proof in
  match g with
  | Typ {goal_meta; goal_hyps; goal_type} ->
    let j_env = List.map pr_hyp goal_hyps in
    `Assoc [
      "typeofgoal", `String "Typ "
    ; "gid", `Int goal_meta.meta_key
    ; "hyps", `List j_env
    ; "type", `String (Format.asprintf "%a" Print.pp_term goal_type)]
  | Unif (ctx,t1,t2) ->
    let constr = Format.asprintf "%a" Print.pp_constr (ctx,t1,t2) in
    `Assoc [
      "typeofgoal", `String "Unif"
    ; "constr", `String constr]

let json_of_goals goals =
  match goals with
  | None ->
    `Null
  | Some goals ->
    `Assoc [
      "goals", `List List.(map json_of_goal goals)
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
