(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant                            *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization arguments                                    *)
(* Copyright 2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

module LSP = Lsp_base

type ast = Parser.p_cmd Pos.loc

type doc_node = {
  ast  : ast;
  exec : bool;
}

(* Private. A doc is a list of nodes for now. The first element in
   the list is assumed to be the tip of the document. The initial
   document is the empty list.
*)
type doc = {
  nodes : doc_node list;
}

let mk_error file version pos msg =
  LSP.mk_diagnostics file version [pos, 1, msg, `Null]

let parse_text contents =
  let open Earley in
  parse_string Parser.cmd_list Parser.blank contents

(* XXX: Imperative problem *)
let json_of_goal (g : Proofs.goal list) =
  let open Proofs in
  let pr_hyp (s,(_,t)) =
    `String (Format.asprintf "%s : %a" s Print.pp_term (Bindlib.unbox t)) in
  let j_env = List.map pr_hyp g.Proofs.g_hyps in
  `Assoc ["hyps", `List j_env;
          "type", `String (Format.asprintf "%a" Print.pp_term g.Proofs.g_type)]

let json_of_goal () =
  let open Timed in
  match !Proofs.theorem with
  | None ->
    `Null
  | Some thm ->
    json_of_goal thm.t_goals

let process_cmd _file (st,dg) node =
  let open Pos  in
  let open Pure in
  (* XXX: Capture output *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  match handle_command st node with
  | OK st ->
    let ok_diag = node.pos, 4, "OK", json_of_goal () in
    st, ok_diag :: dg
  | Error (_loc, msg) ->
    st, (node.pos, 1, msg, `Null) :: dg

let new_doc modname = Pure.initial_state modname

(* XXX: Save on close. *)
let close_doc _modname = ()

let check_text ~doc file version contents =
  try
    let doc_spans = parse_text contents in
    let _st, diag = List.fold_left (process_cmd file) (doc,[]) doc_spans in
    LSP.mk_diagnostics file version @@ List.fold_left (fun acc (pos,lvl,msg,goal) ->
        match pos with
        | None     -> acc
        | Some pos -> (pos,lvl,msg,goal) :: acc
      ) [] diag
  with
  | Earley.Parse_error(buf,pos) ->
    let loc = Pos.locate buf pos buf pos in
    mk_error file version loc "Parse error."
