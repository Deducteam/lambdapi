open Lplib
open Timed
open Core
open Common open Error open Library
open Parsing
open Handle
open Base

(* Should be lifted *)
module Util = struct

  let located pp ppf ({Pos.pos; _} as e) =
    let pos = Option.map Pos.to_string pos in
    out ppf "[%a] %a" (Option.pp string) pos pp e

end

(** Representation of a single command (abstract). *)
module Command = struct
  type t = Syntax.p_command
  let equal = Syntax.eq_p_command
  let get_pos c = Pos.(c.pos)
  let print = Util.located Pretty.command
end

let interval_of_pos : Pos.pos -> Range.t =
  fun {start_line; start_col; end_line; end_col; _} ->
  let open Range in
  let start : point = make_point start_line start_col in
  let finish : point = make_point end_line end_col in
  make_interval start finish

(** Document identifier range map. *)
let rangemap : Command.t list -> Term.qident RangeMap.t =
  let f map ({elt;pos} : Syntax.p_qident) =
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
  let print = Util.located Pretty.tactic
end

(** Representation of a single proof (abstract). *)
module ProofTree = struct
  type t = Syntax.p_proof
  let equal = Syntax.eq_p_proof
  let fold = Syntax.fold_proof
end

type state = Time.t * Sig_state.t

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos * string

let parse_text : state -> fname:string -> string -> Command.t list * state =
    fun (t,st) ~fname s ->
  let dk_syntax = Filename.check_suffix fname dk_src_extension in
  try
    LibMeta.reset_meta_counter();
    Time.restore t;
    let ast =
      let strm =
        if dk_syntax then Parser.Dk.parse_string fname s
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
  Time.t * Sig_state.t * Proof.proof_state * proof_finalizer * bool * Pos.popt

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
  fun g ->
  let open Print in
  let bctx = Proof.Goal.bindlib_ctxt g in
  let term = term_in bctx in
  let env_elt (s,(_,t,_)) = s, to_string term (Bindlib.unbox t) in
  let ctx_elt (x,a,_) = to_string var x, to_string term a in
  match g with
  | Proof.Typ gt ->
      let meta = to_string meta gt.goal_meta in
      let typ = to_string term gt.goal_type in
      List.rev_map env_elt gt.goal_hyps, Typ (meta, typ)
  | Proof.Unif (c,t,u) ->
      let t = to_string term t and u = to_string term u in
      List.rev_map ctx_elt c, Unif (t,u)

let current_goals : proof_state -> goal list =
  fun (time, st, ps, _, _, _) ->
  Time.restore time;
  Print.sig_state := st;
  List.map string_of_goal ps.proof_goals

type command_result =
  | Cmd_OK    of state * string option
  | Cmd_Proof of proof_state * ProofTree.t * Pos.popt * Pos.popt
  | Cmd_Error of Pos.popt option * string

type tactic_result =
  | Tac_OK    of proof_state * string option
  | Tac_Error of Pos.popt option * string

let t0 : Time.t Stdlib.ref = Stdlib.ref (Time.save ())

let set_initial_time : unit -> unit = fun _ ->
  Stdlib.(t0 := Time.save ())

let initial_state : string -> state = fun fname ->
  Console.reset_default ();
  Time.restore Stdlib.(!t0);
  Package.apply_config fname;
  let mp = Library.path_of_file LpLexer.escape fname in
  Sign.loading := [mp];
  let sign = Sig_state.create_sign mp in
  Sign.loaded  := Path.Map.add mp sign !Sign.loaded;
  (Time.save (), Sig_state.of_sign sign)

let handle_command : state -> Command.t -> command_result =
  fun (st,ss) cmd ->
  Time.restore st;
  let open Handle in
  try
    let (ss, ps, qres) = Command.get_proof_data Compile.compile ss cmd in
    let t = Time.save () in
    match ps with
    | None ->
        let qres = Option.map (fun f -> f ()) qres in Cmd_OK ((t, ss), qres)
    | Some(d) ->
      let ps =
        (t, ss, d.pdata_state, d.pdata_finalize, d.pdata_prv, d.pdata_sym_pos)
      in
        Cmd_Proof(ps, d.pdata_proof, d.pdata_sym_pos, d.pdata_end_pos)
  with Fatal(Some p,m) ->
    Cmd_Error(Some p, Pos.popt_to_string p ^ m)

let handle_tactic : proof_state -> Tactic.t -> int -> tactic_result =
  fun (_, ss, ps, finalize, prv, sym_pos) tac n ->
  try
    let ps, qres = Handle.Tactic.handle ss sym_pos prv (ps, None) tac n in
    let qres = Option.map (fun f -> f ()) qres in
    Tac_OK((Time.save (), ss, ps, finalize, prv, sym_pos), qres)
  with Fatal(Some p,m) ->
    Tac_Error(Some p, Pos.popt_to_string p ^ m)

let end_proof : proof_state -> command_result =
  fun (_, ss, ps, finalize, _, _) ->
  try Cmd_OK((Time.save (), finalize ss ps), None)
  with Fatal(Some p,m) ->
    Cmd_Error(Some p, Pos.popt_to_string p ^ m)

let get_symbols : state -> Term.sym Extra.StrMap.t =
  fun (_, ss) -> ss.in_scope
