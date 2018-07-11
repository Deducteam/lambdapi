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
  uri : string;
  version: int;
  text : string;
  root : Pure.state;
  nodes : doc_node list;
}

let mk_error ~doc pos msg =
  LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None]

let parse_text contents =
  let open Earley in
  parse_string Parser.cmd_list Parser.blank contents

(* XXX: Imperative problem *)
let process_cmd _file (st,dg) node =
  let open Pos  in
  let open Pure in
  let open Timed in
  (* XXX: Capture output *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  match handle_command st node with
  | OK st ->
    let ok_diag = node.pos, 4, "OK", !Proofs.theorem in
    st, ok_diag :: dg
  | Error (_loc, msg) ->
    st, (node.pos, 1, msg, None) :: dg

let new_doc ~uri ~version ~text =
  { uri;
    text;
    version;
    root = Pure.initial_state [LSP.parse_uri uri];
    nodes = [];
  }

(* XXX: Save on close. *)
let close_doc _modname = ()

let check_text ~doc =
  let uri, version = doc.uri, doc.version in
  try
    let doc_spans = parse_text doc.text in
    let st, diag = List.fold_left (process_cmd uri) (doc.root,[]) doc_spans in
    st, LSP.mk_diagnostics ~uri ~version @@ List.fold_left (fun acc (pos,lvl,msg,goal) ->
        match pos with
        | None     -> acc
        | Some pos -> (pos,lvl,msg,goal) :: acc
      ) [] diag
  with
  | Earley.Parse_error(buf,pos) ->
    let loc = Pos.locate buf pos buf pos in
    doc.root, mk_error ~doc loc "Parse error."
