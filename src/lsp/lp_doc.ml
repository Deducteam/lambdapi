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

(* exception NoPosition of string *)

module type RangeMap = sig

  type point
  type interval
  type 'a t

  val create_point : int -> int -> point
  val l : point -> int
  val c : point -> int

  val interval_start : interval -> point
  val interval_end : interval -> point

  val create_interval : point -> point -> interval

  type cmp = Before | In | After

  val in_range : point -> interval -> cmp

  val add : interval -> 'a -> 'a t -> 'a t
  val find : point -> 'a t -> 'a option * interval

  val empty : 'a t

  val rangemap_to_string : ('a * string) t -> string
end

module M : RangeMap = struct

  type point = { l : int; c : int }

  type interval = point * point

  let create_point l c = { l = l; c = c}

  let l pt = pt.l

  let c pt = pt .c

  let interval_start (x, _) = x

  let interval_end (_, y) = y

  let create_interval x y =
    assert ( (l x < l y) || (l x = l y && c x <= c y) );
    (x, y)

  type cmp = Before | In | After

  let in_range pos (pos1, pos2) =

    if pos.l < pos1.l || (pos.l = pos1.l && pos.c < pos1.c)
    then Before

    else if pos.l > pos2.l || (pos.l = pos2.l && pos.c > pos2.c)
    then After

    else In

  type 'a t = (interval * 'a) list

  let rec find (cursor_pos : point) (l: 'a t) = match l with
    |(interval, elt)::t ->
      if in_range cursor_pos interval = In
      then (Some elt, interval)

      else find cursor_pos t
    |_ -> (None, (create_point 0 0, create_point 0 0))

  let add (k:interval) (elt:'a) (l :'a t) = (k, elt)::l

  let empty = []

  let rec rangemap_to_string (map :  (_ * string) t) = match map with
    | [] -> "End"
    | h::t -> let ( ({l = sl; c = sc}, {l = fl; c= fc}), (_ , str) ) = h in
    (string_of_int sl)^","^(string_of_int sc)^"|"^(string_of_int fl)^","
    ^(string_of_int fc)^":"^str^"\n"^(rangemap_to_string t)
end

let interval_of_pos (p : Pos.pos) = let open M in

  let data = Lazy.force p in
  let start : point = create_point data.start_line data.start_col in
  let finish : point = create_point data.end_line data.end_col in

  create_interval start finish

let interval_of_popt (p : Pos.popt) = match p with
  | None -> failwith "interval_of_popt : no position given for the token"
  | Some pos -> interval_of_pos pos


let rec maplist_of_p_command_list (doc : Syntax.qident list) = match doc with
    | [] -> []
    | h::t -> (h.pos, h.elt)::(maplist_of_p_command_list t)


type doc_node =
  { ast   : Pure.Command.t
  ; exec  : bool
  (*; tactics : Proof.Tactic.t list*)
  ; goals : (Proof.Goal.t list * Pos.popt) list
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
  map : (Syntax.p_module_path * string) M.t;
  str_map : string
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
    let goals = Some (current_goals pstate) in
    pstate, (tac_loc, 4, "OK", goals) :: diags
  | Tac_Error(loc,msg) ->
    let loc = option_default loc tac_loc in
    pstate, (loc, 1, msg, None) :: diags

let process_proof pstate tacs =
  List.fold_left process_pstep (pstate,[]) tacs

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
let process_cmd _file (nodes,st,dg) ast =
  let open Pure in
  (* let open Timed in *)
  (* XXX: Capture output *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  let cmd_loc = Command.get_pos ast in
  match handle_command st ast with
  | Cmd_OK st ->
    let nodes = { ast; exec = true; goals = [] } :: nodes in
    let ok_diag = cmd_loc, 4, "OK", None in
    nodes, st, ok_diag :: dg

  | Cmd_Proof (pst, tlist, thm_loc, qed_loc) ->
    let start_goals = current_goals pst in
    let pst, dg_proof = process_proof pst tlist in
    let dg_proof = (thm_loc, 4, "OK", Some start_goals) :: dg_proof in
    let goals = get_goals dg_proof in
    let nodes = { ast; exec = true; goals } :: nodes in
    let st, dg_proof =
      match end_proof pst with
      | Cmd_OK st          ->
        let pg = qed_loc, 4, "OK", None in
        st, pg :: dg_proof
      | Cmd_Error(_loc,msg) ->
        let pg = qed_loc, 1, msg, None in
        st, pg :: dg_proof
      | Cmd_Proof _ ->
        Lsp_io.log_error "process_cmd" "closing proof is nested";
        assert false
    in
    nodes, st, dg_proof @ dg

  | Cmd_Error(loc, msg) ->
    let nodes = { ast; exec = false; goals = [] } :: nodes in
    let loc = option_default loc Command.(get_pos ast) in
    nodes, st, (loc, 1, msg, None) :: dg

let new_doc ~uri ~version ~text =
  let root =
    (* We remove the ["file://"] prefix. *)
    assert(Extra.String.is_prefix "file://" uri);
    let path = String.sub uri 7 (String.length uri - 7) in
    Pure.initial_state path
  in
  { uri;
    text;
    version;
    root;
    final = root;
    nodes = [];
    map = M.empty;
    str_map = ""
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

let concat_map (f:'a -> 'b list) (l: 'a list) : 'b list =
  List.concat (List.map f l)

let check_text ~doc =
  let uri, version = doc.uri, doc.version in
  try
    let doc_spans =
      let (doc_spans, root) = Pure.parse_text doc.root uri doc.text in
      (* One shot state update after parsing. *)
      doc.root <- root; doc.final <- root; doc_spans
    in

    (*doc spans are converted to q_idents, which are basically tokens with a
    position*)
    let qids = concat_map Pure.Command.get_qidents doc_spans in

    (*these qidents are then converted to a map*)
    let f (map : (Syntax.p_module_path * string) M.t) (qid : Syntax.qident) =
      M.add (interval_of_popt qid.pos) qid.elt map in

    let map = List.fold_left f M.empty qids in
    let str_map = M.rangemap_to_string map in

    let nodes, final, diag =
      List.fold_left (process_cmd uri) ([],doc.root,[]) doc_spans in
    let doc = { doc with nodes; final; map; str_map } in
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
