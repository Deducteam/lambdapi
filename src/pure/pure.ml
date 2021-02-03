open! Lplib

open Timed
open Core
open Common
open Parsing
open Console
open Module
open Handle

(** Representation of a single command (abstract). *)
module Command = struct
  type t = Syntax.p_command
  let equal = Syntax.eq_p_command
  let get_pos c = Pos.(c.pos)
end

let interval_of_pos : Pos.pos -> Range.t =
  fun {start_line; start_col; end_line; end_col; _} ->
  let open Range in
  let start : point = make_point start_line start_col in
  let finish : point = make_point end_line end_col in
  make_interval start finish

(** Document identifier range map. *)
let rangemap : Command.t list -> Syntax.qident_aux RangeMap.t =
  let f map ({elt;pos} : Syntax.qident) =
    (* Only add if the symbol has a position. *)
    match pos with
    | Some pos -> RangeMap.add (interval_of_pos pos) elt map
    | None -> map
  in
  Syntax.fold_idents f RangeMap.empty

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
      let strm =
        if old_syntax then Parser.Dk.parse_string fname s
        else Parser.parse_string fname s
      in
      (* NOTE this processing could be avoided with a parser for a list of
         commands. Such a parser is not trivially done. *)
      let cmds = Stdlib.ref [] in
      Stream.iter (fun c -> Stdlib.(cmds := c :: !cmds)) strm;
      List.rev Stdlib.(!cmds)
    in
    (ast, (Time.save (), st))
  with
  | Fatal(Some(Some(pos)), msg) -> raise (Parse_error(pos, msg))
  | Fatal(Some(None)     , _  ) -> assert false (* Should not produce. *)
  | Fatal(None           , _  ) -> assert false (* Should not produce. *)

type proof_finalizer = Sig_state.t -> Proof.proof_state -> Sig_state.t
type proof_state =
  Time.t * Sig_state.t * Proof.proof_state * proof_finalizer *
  Syntax.Tags.expo
type conclusion =
  | Typ of string * string
  | Unif of string * string
type goal = (string * string) list * conclusion

let string_of_goal : Proof.goal -> goal =
  let buf = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer buf in
  let to_string f x =
    f fmt x;
    Format.pp_print_flush fmt ();
    let res = Buffer.contents buf in
    Buffer.clear buf;
    res
  in
  let open Print in
  let env_elt (s,(_,t,_)) = s, to_string pp_term (Bindlib.unbox t) in
  let ctx_elt (x,a,_) = to_string pp_var x, to_string pp_term a in
  fun g ->
  match g with
  | Proof.Typ gt ->
      let meta = to_string pp_meta gt.goal_meta in
      let typ = to_string pp_term gt.goal_type in
      List.rev_map env_elt gt.goal_hyps, Typ (meta, typ)
  | Proof.Unif (c,t,u) ->
      let t = to_string pp_term t and u = to_string pp_term u in
      List.rev_map ctx_elt c, Unif (t,u)

let current_goals : proof_state -> goal list =
  fun (time, st, ps, _, _) ->
  Time.restore time;
  Print.sig_state := st;
  List.map string_of_goal ps.proof_goals

type command_result =
  | Cmd_OK    of state * Query.result
  | Cmd_Proof of proof_state * Tactic.t list * Pos.popt * Pos.popt
  | Cmd_Error of Pos.popt option * string

type tactic_result =
  | Tac_OK    of proof_state * Query.result
  | Tac_Error of Pos.popt option * string

let t0 : Time.t Stdlib.ref = Stdlib.ref (Time.save ())

let set_initial_time : unit -> unit = fun _ ->
  Stdlib.(t0 := Time.save ())

let initial_state : file_path -> state = fun fname ->
  Console.reset_default ();
  Time.restore Stdlib.(!t0);
  Package.apply_config fname;
  let mp = Module.file_to_module fname in
  Sign.loading := [mp];
  let sign = Sig_state.create_sign mp in
  Sign.loaded  := PathMap.add mp sign !Sign.loaded;
  (Time.save (), Sig_state.of_sign sign)

let handle_command : state -> Command.t -> command_result =
    fun (st,ss) cmd ->
  Time.restore st;
  let open Handle in
  try
    let (ss, pst, qres) = Command.handle (Compile.compile false) ss cmd in
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
    let p, qres = Handle.Tactic.handle ss e p t in
    Tac_OK((Time.save (), ss, p, finalize, e), qres)
  with Fatal(p,m) -> Tac_Error(p,m)

let end_proof : proof_state -> command_result = fun s ->
  let (_, ss, p, finalize, _) = s in
  try Cmd_OK((Time.save (), finalize ss p), None)
  with Fatal(p,m) -> Cmd_Error(p,m)

let get_symbols : state -> (Term.sym * Pos.popt) Extra.StrMap.t = fun s ->
  (snd s).in_scope
