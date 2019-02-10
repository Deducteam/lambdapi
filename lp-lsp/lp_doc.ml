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

open Core
module LSP = Lsp_base

type doc_node = {
  ast  : Syntax.command;
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
  root : Pure.command_state;
  nodes : doc_node list;
}

let option_default o1 d =
  match o1 with | None -> d | Some x -> x

let mk_error ~doc pos msg =
  LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None]

let process_pstep (pstate, diags) tac =
  let open Pure in
  let tac_loc = Tactic.get_pos tac in
  match handle_tactic pstate tac with
  | Tac_OK pstate ->
    (* Fixme *)
    let goals = None in
    pstate, (tac_loc, 4, "OK", goals) :: diags
  | Tac_Error(loc,msg) ->
    let loc = option_default loc tac_loc in
    pstate, (loc, 1, msg, None) :: diags

let process_proof pstate tacs =
  List.fold_left process_pstep (pstate,[]) tacs

(* XXX: Imperative problem *)
let process_cmd _file (st,dg) node =
  let open Pure in
  (* let open Timed in *)
  (* XXX: Capture output *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  let cmd_loc = Command.get_pos node in
  match handle_command st node with
  | Cmd_OK st ->
    (* let ok_diag = node.pos, 4, "OK", !Proofs.theorem in *)
    let ok_diag = cmd_loc, 4, "OK", None in
    st, ok_diag :: dg
  | Cmd_Proof (pst, tlist, _, _) -> (* FIXME use positions. *)
    let pst, dg_proof = process_proof pst tlist in
    (* Fixme: this throws and exception and it should not *)
    let st, dg_proof =
      match end_proof pst with
      | Cmd_OK st          -> (st, dg_proof)
      | Cmd_Error(loc,msg) ->
          let loc = option_default loc cmd_loc in
          let _pg = (loc, 1, msg, None) in
          (* We don't add the diagnostic as it shadows the internal
             ones; we should refine the loc to the qed *)
          st, dg_proof
      | Cmd_Proof(_,_,_,_) -> assert false (* Cannot happen. *)
    in
    st, dg_proof @ dg
  | Cmd_Error(_loc, msg) ->
    st, (Command.get_pos node, 1, msg, None) :: dg

let new_doc ~uri ~version ~text =
  { uri;
    text;
    version;
    root = Pure.initial_state [uri];
    nodes = [];
  }

(* XXX: Save on close. *)
let close_doc _modname = ()

let check_text ~doc =
  let uri, version = doc.uri, doc.version in
  try
    let doc_spans = Pure.parse_text uri doc.text in
    let st, diag = List.fold_left (process_cmd uri) (doc.root,[]) doc_spans in
    st, LSP.mk_diagnostics ~uri ~version @@ List.fold_left (fun acc (pos,lvl,msg,goal) ->
        match pos with
        | None     -> acc
        | Some pos -> (pos,lvl,msg,goal) :: acc
      ) [] diag
  with
  | Pure.Parse_error(loc, msg) -> doc.root, mk_error ~doc loc msg
