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

open Common
open Lplib
open Handle

module LSP = Lsp_base

(* exception NoPosition of string *)

(* Buffer for storing the log messages *)
let lp_logger = Buffer.create 100

type doc_node =
  { ast   : Pure.Command.t
  ; exec  : bool
  (*; tactics : Proof.Tactic.t list*)
  ; goals : (Goal.info list * Pos.popt) list
  }

(* Private. A doc is a list of nodes for now. The first element in
   the list is assumed to be the tip of the document. The initial
   document is the empty list.
*)
type t = {
  uri : string;
  version: int;
  text : string;
  mutable root  : Pure.state option; (* Only mutated after parsing. *)
  mutable final : Pure.state option; (* Only mutated after parsing. *)
  nodes : doc_node list;
  (* severity is same as LSP specifications : https://git.io/JiGAB *)
  logs : ((int * string) * Pos.popt) list; (*((severity, message), location)*)
  map : Core.Term.qident RangeMap.t;
}

let option_default o1 d =
  match o1 with | None -> d | Some x -> x

let mk_error ~doc pos msg =
  LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None]

let buf_get_and_clear buf =
  let res = Buffer.contents buf in
  Buffer.clear buf; res

let process_pstep (pstate,diags,logs) tac nb_subproofs =
  let open Pure in
  let tac_loc = Tactic.get_pos tac in
  let hndl_tac_res = handle_tactic pstate tac nb_subproofs in
  let logs = ((3, buf_get_and_clear lp_logger), tac_loc) :: logs in
  match hndl_tac_res with
  | Tac_OK (pstate, qres) ->
    let goals = Some (current_goals pstate) in
    let qres = match qres with None -> "Tactic succeded" | Some x -> x in
    pstate, (tac_loc, 4, qres, goals) :: diags, logs
  | Tac_Error(loc,msg) ->
    let loc = option_default loc tac_loc in
    let goals = Some (current_goals pstate) in
    pstate, (loc, 1, msg, goals) :: diags, ((1, msg), loc) :: logs

let process_proof pstate tacs logs =
  Pure.ProofTree.fold process_pstep (pstate,[],logs) tacs

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
  let logs = ((3, buf_get_and_clear lp_logger), cmd_loc) :: logs in
  match hndl_cmd_res with
  | Cmd_OK (st, qres) ->
    let qres = match qres with None -> "Command succeded" | Some x -> x in
    let nodes = { ast; exec = true; goals = [] } :: nodes in
    let ok_diag = cmd_loc, 4, qres, None in
    nodes, st, ok_diag :: dg, logs
  | Cmd_Proof (pst, tlist, thm_loc, qed_loc, qres) ->
    let name = Pure.name_of_proof pst in
    let start_goals = current_goals pst in
    let pst, dg_proof, logs = process_proof pst tlist logs in
    let dg_proof =
      (thm_loc, 4, "symbol "^name^" successfully defined", Some start_goals)
      :: dg_proof in
    let goals = get_goals dg_proof in
    let nodes = { ast; exec = true; goals } :: nodes in
    let st, dg_proof, logs =
      match end_proof pst with
      | Cmd_OK (st, _qres)   ->
        let dg_proof = match qres with
        | None -> dg_proof
        | Some x ->  let pg = qed_loc, 4, x, None in pg :: dg_proof
      in
        (* let pg = qed_loc, 4, qres, None in *)
        let logs = ((3, buf_get_and_clear lp_logger), cmd_loc) :: logs in
        st, dg_proof, logs
      | Cmd_Error(_loc,msg) ->
        let pg = qed_loc, 1, msg, None in
        st, pg :: dg_proof, ((1, msg), qed_loc) :: logs
      | Cmd_Proof _ ->
        Lsp_io.log_error "process_cmd" "closing proof is nested";
        assert false
    in
    nodes, st, dg_proof @ dg, logs

  | Cmd_Error(loc, msg) ->
    let nodes = { ast; exec = false; goals = [] } :: nodes in
    let cmd_loc, loc = match cmd_loc, loc with
    | Some l, Some Some l' ->
        if l.fname = l'.fname then
          (* if error in the same file, use the precise location *)
          Some l', Some l'
        else
          (* else, use the location of the command *)
          cmd_loc, Some l'
    (* Otherwise,
      cmd_loc doesn't change and loc is : option_default loc cmd_loc *)
    | _, Some l' -> cmd_loc, l'
    | _, None -> cmd_loc, cmd_loc in
    nodes, st, (cmd_loc, 1, msg, None) :: dg, ((1, msg), loc) :: logs

let new_doc ~uri ~version ~text =
  let root, logs =
    try
      let uri = Uri.pct_decode uri in
      (* We remove the ["file://"] prefix. *)
      assert(String.is_prefix "file://" uri);
      let path = String.sub uri 7 (String.length uri - 7) in
      Some(Pure.initial_state path), []
    with Error.Fatal(_pos, msg) ->
      let loc : Pos.pos =
        {
          fname = Some(uri);
          start_line = 0;
          start_col  = 0;
          start_offset  = 0;
          end_line = 0;
          end_col = 0;
          end_offset  = 0
        } in
      (None, [(1, msg), Some(loc)])
  in
  { uri;
    text;
    version;
    root;
    final = root;
    nodes = [];
    logs = logs;
    map = RangeMap.empty;
  }

(* XXX: Save on close. *)
let close_doc _modname = ()

let dummy_loc =
  Lazy.from_val
    Pos.{ fname = None
        ; start_line = 1
        ; start_col = 1
        ; start_offset = -1
        ; end_line = 2
        ; end_col = 2
        ; end_offset = -1
        }

let check_text ~doc =
  let uri, version = doc.uri, doc.version in
  let cmds, error = Pure.parse_text ~fname:uri doc.text in
  let root =
    match doc.root with
    | Some ss -> ss
    | None ->
        raise(Error.fatal_no_pos "Root state is missing probably because \
                                  new_doc raised an exception")
  in
  let nodes, final, diags, logs =
    List.fold_left (process_cmd uri) ([],root,[],[]) cmds in
  let logs = List.rev logs
  and diags = (* filter out diagnostics with no position *)
    List.fold_left (fun acc (pos,lvl,msg,goal) ->
        match pos with
        | None     -> acc
        | Some pos -> (pos,lvl,msg,goal) :: acc
      ) [] diags
  in
  let logs, diags =
    match error with
    | None -> logs, diags
    | Some(pos,msg) -> logs @ [((1, msg), Some pos)], diags @ [pos,1,msg,None]
  in
  let map = Pure.rangemap cmds in
  let doc = { doc with nodes; final=Some(final); map; logs } in
  doc, LSP.mk_diagnostics ~uri ~version diags
