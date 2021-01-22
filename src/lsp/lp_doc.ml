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
open! Lplib

module LSP = Lsp_base

(* exception NoPosition of string *)

(* Buffer for storing the log messages *)
let lp_logger = Buffer.create 100

let interval_of_pos : Pos.pos -> Range.t = fun p ->
  let open Range in
  let start : point = make_point p.start_line p.start_col in
  let finish : point = make_point p.end_line p.end_col in
  make_interval start finish

type doc_node =
  { ast   : Pure.Command.t
  ; exec  : bool
  (*; tactics : Proof.Tactic.t list*)
  ; goals : (Pure.goal list * Pos.popt) list
  }

(* Private. A doc is a list of nodes for now. The first element in
   the list is assumed to be the tip of the document. The initial
   document is the empty list.
*)
type t = {
  uri : string;
  version: int;
  text : string;
  mutable root  : Pure.state; (* Only mutated after parsing. *)
  mutable final : Pure.state; (* Only mutated after parsing. *)
  nodes : doc_node list;
  logs : (string * Pos.popt) list;
  map : (Syntax.p_module_path * string) RangeMap.t;
}

let option_default o1 d =
  match o1 with | None -> d | Some x -> x

let mk_error ~doc pos msg =
  LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None]

let buf_get_and_clear buf =
  let res = Buffer.contents buf in
  Buffer.clear buf; res

let process_pstep (pstate,diags,logs) tac =
  let open Pure in
  let tac_loc = Tactic.get_pos tac in
  let hndl_tac_res = handle_tactic pstate tac in
  let logs = (buf_get_and_clear lp_logger, tac_loc) :: logs in
  match hndl_tac_res with
  | Tac_OK (pstate, qres) ->
    let goals = Some (current_goals pstate) in
    let qres = match qres with None -> "OK" | Some x -> x in
    pstate, (tac_loc, 4, qres, goals) :: diags, logs
  | Tac_Error(loc,msg) ->
    let loc = option_default loc tac_loc in
    pstate, (loc, 1, msg, None) :: diags, logs

let process_proof pstate tacs logs =
  List.fold_left process_pstep (pstate,[],logs) tacs

let get_goals dg_proof =
  let rec get_goals_aux goals dg_proof =
    match dg_proof with
    | [] -> goals
    | (loc,_,_, Some goalsList)::s ->
        let g = (goals @ [goalsList, loc]) in get_goals_aux g s
    | (loc,_,_,None)::s ->
        let goals = (goals @ [[], loc]) in get_goals_aux goals s
  in get_goals_aux [] dg_proof
(* XXX: Imperative problem *)
let process_cmd _file (nodes,st,dg,logs) ast =
  let open Pure in
  (* let open Timed in *)
  (* XXX: Capture output *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  let cmd_loc = Command.get_pos ast in
  let hndl_cmd_res = handle_command st ast in
  let logs = (buf_get_and_clear lp_logger, cmd_loc) :: logs in
  match hndl_cmd_res with
  | Cmd_OK (st, qres) ->
    let qres = match qres with None -> "OK" | Some x -> x in
    let nodes = { ast; exec = true; goals = [] } :: nodes in
    let ok_diag = cmd_loc, 4, qres, None in
    nodes, st, ok_diag :: dg, logs

  | Cmd_Proof (pst, tlist, thm_loc, qed_loc) ->
    let start_goals = current_goals pst in
    let pst, dg_proof, logs = process_proof pst tlist logs in
    let dg_proof = (thm_loc, 4, "OK", Some start_goals) :: dg_proof in
    let goals = get_goals dg_proof in
    let nodes = { ast; exec = true; goals } :: nodes in
    let st, dg_proof =
      match end_proof pst with
      | Cmd_OK (st, qres)   ->
        let qres = match qres with None -> "OK" | Some x -> x in
        let pg = qed_loc, 4, qres, None in
        st, pg :: dg_proof
      | Cmd_Error(_loc,msg) ->
        let pg = qed_loc, 1, msg, None in
        st, pg :: dg_proof
      | Cmd_Proof _ ->
        Lsp_io.log_error "process_cmd" "closing proof is nested";
        assert false
    in
    nodes, st, dg_proof @ dg, logs

  | Cmd_Error(loc, msg) ->
    let nodes = { ast; exec = false; goals = [] } :: nodes in
    let loc = option_default loc Command.(get_pos ast) in
    nodes, st, (loc, 1, msg, None) :: dg, logs

let new_doc ~uri ~version ~text =
  let root =
    (* We remove the ["file://"] prefix. *)
    assert(String.is_prefix "file://" uri);
    let path = String.sub uri 7 (String.length uri - 7) in
    Pure.initial_state path
  in
  { uri;
    text;
    version;
    root;
    final = root;
    nodes = [];
    logs = [];
    map = RangeMap.empty;
  }

(* XXX: Save on close. *)
let close_doc _modname = ()

let dummy_loc =
  Lazy.from_val
    Pos.{ fname = None
        ; start_line = 1
        ; start_col = 1
        ; end_line = 2
        ; end_col = 2
        }

(** Update document identifier range map *)
let update_rangemap doc_spans =
  (* extract q_idents from spans *)
  let qids = List.concat_map Pure.Command.get_qidents doc_spans in

  (* add to the map *)
  let f (map : (Syntax.p_module_path * string) RangeMap.t)
        (qid : Syntax.qident) =
    (* Only add if the symbol contains a position *)
    Option.map_default
      (fun pos -> RangeMap.add (interval_of_pos pos) qid.elt map)
      map qid.pos
  in
  List.fold_left f RangeMap.empty qids

let check_text ~doc =
  let uri, version = doc.uri, doc.version in
  try
    let doc_spans =
      let (doc_spans, root) = Pure.parse_text doc.root uri doc.text in
      (* One shot state update after parsing. *)
      doc.root <- root; doc.final <- root; doc_spans
    in

    (* update rangemap *)
    let map = update_rangemap doc_spans in

    let nodes, final, diag, logs =
      List.fold_left (process_cmd uri) ([],doc.root,[],[]) doc_spans in
    let logs = List.rev logs in
    let doc = { doc with nodes; final; map; logs } in
    doc,
    LSP.mk_diagnostics ~uri ~version @@
    List.fold_left (fun acc (pos,lvl,msg,goal) ->
        match pos with
        | None     -> acc
        | Some pos -> (pos,lvl,msg,goal) :: acc
      ) [] diag
  with
  | Pure.Parse_error(loc, msg) ->
    doc, mk_error ~doc loc msg
