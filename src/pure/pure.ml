open! Lplib

open Timed
open Core
open Console
open Files

(** Representation of a single command (abstract). *)
module Command = struct
  type t = Syntax.p_command
  let equal = Syntax.eq_p_command
  let get_pos c = Pos.(c.pos)
  let get_qidents = Cmd_analysis.get_qidents
end

(** Representation of a single tactic (abstract). *)
module Tactic = struct
  type t = Syntax.p_tactic
  let equal = Syntax.eq_p_tactic
  let get_pos t = Pos.(t.pos)
end

type state = Time.t * Sig_state.t

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos * string

let parse_text : state -> string -> string -> Command.t list * state =
    fun (t,st) fname s ->
  let old_syntax = Filename.check_suffix fname legacy_src_extension in
  try
    Time.restore t;
    let ast =
      if old_syntax then Legacy_parser.parse_string fname s
      else Parser.parse_string fname s
    in
    (ast, (Time.save (), st))
  with
  | Fatal(Some(Some(pos)), msg) -> raise (Parse_error(pos, msg))
  | Fatal(Some(None)     , _  ) -> assert false (* Should not produce. *)
  | Fatal(None           , _  ) -> assert false (* Should not produce. *)

type proof_finalizer = Sig_state.t -> Proof.t -> Sig_state.t
type proof_state =
  Time.t * Sig_state.t * Proof.t * proof_finalizer * Terms.expo

let current_goals : proof_state -> Proof.Goal.t list = fun (_,_,p,_,_) ->
  p.proof_goals

type command_result =
  | Cmd_OK    of state * Queries.q_res
  | Cmd_Proof of proof_state * Tactic.t list * Pos.popt * Pos.popt
  | Cmd_Error of Pos.popt option * string

type tactic_result =
  | Tac_OK    of proof_state * Queries.q_res
  | Tac_Error of Pos.popt option * string

let t0 : Time.t Stdlib.ref = Stdlib.ref (Time.save ())

let set_initial_time : unit -> unit = fun _ ->
  Stdlib.(t0 := Time.save ())

let get_initial_time : unit -> Time.t = fun _ ->
  Stdlib.(!t0)

let initial_state : file_path -> state = fun fname ->
  Console.reset_default ();
  Time.restore Stdlib.(!t0);
  Package.apply_config fname;
  let mp = Files.file_to_module fname in
  Sign.loading := [mp];
  let sign = Sig_state.create_sign mp in
  Sign.loaded  := PathMap.add mp sign !Sign.loaded;
  let tempoc = open_out_gen [Open_append; Open_creat] 0o666 "aksdjfla.txt" in
  Printf.fprintf tempoc "%B\n%!" Timed.(!Console.log_enabled);
  close_out tempoc;
  (Time.save (), Sig_state.of_sign sign)

let handle_command : state -> Command.t -> command_result =
    fun (st,ss) cmd ->
  Time.restore st;
  try
    let (ss, pst, qres) = Handle.handle_cmd ss cmd in
    let t = Time.save () in
    match pst with
    | None       -> Cmd_OK ((t, ss), qres)
    | Some(data) ->
        let pst =
          (t, ss, data.pdata_p_state, data.pdata_finalize, data.pdata_expo) in
        let ts = data.pdata_tactics in
        Cmd_Proof(pst, ts, data.pdata_stmt_pos, data.pdata_end_pos)
  with Fatal(p,m) -> Cmd_Error(p,m)

let handle_tactic : proof_state -> Tactic.t -> tactic_result =
  fun s t ->
  let (_, ss, p, finalize, e) = s in
  try
    let p, qres = Tactics.handle_tactic ss e p t in
    Tac_OK((Time.save (), ss, p, finalize, e), qres)
  with Fatal(p,m) -> Tac_Error(p,m)

let end_proof : proof_state -> command_result = fun s ->
  let (_, ss, p, finalize, _) = s in
  try Cmd_OK((Time.save (), finalize ss p), None) with Fatal(p,m) -> Cmd_Error(p,m)

let get_symbols : state -> (Terms.sym * Pos.popt) Extra.StrMap.t = fun s ->
  (snd s).in_scope
