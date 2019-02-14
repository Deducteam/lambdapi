(** Interface to lp-lsp. *)

open Timed

(* Lambdapi core *)
open Core
open Core.Extra
open Core.Console

(* NOTE this is required for initialization of [Parser.require]. *)
let _ = Compile.compile

(** Representation of a single command (abstract). *)
module Command = struct
  type t = Syntax.command
  let equal = Syntax.eq_command
  let get_pos c = Pos.(c.pos)
end

(** Representation of a single tactic (abstract). *)
module Tactic = struct
  type t = Syntax.p_tactic
  let equal = Syntax.eq_p_tactic
  let get_pos t = Pos.(t.pos)
end

(** Exception raised by [parse_text] on error. *)
exception Parse_error of Pos.pos * string

let parse_text : string -> string -> Command.t list = fun fname s ->
  let old_syntax = Filename.check_suffix fname Files.legacy_src_extension in
  try
    if old_syntax then Legacy_parser.parse_string fname s
    else Parser.parse_string fname s
  with
  | Fatal(Some(Some(pos)), msg) -> raise (Parse_error(pos, msg))
  | Fatal(Some(None)     , _  ) -> assert false (* Should not produce. *)
  | Fatal(None           , _  ) -> assert false (* Should not produce. *)

type command_state = Time.t * Scope.sig_state

type proof_finalizer = Scope.sig_state -> Proof.t -> Scope.sig_state
type proof_state = Time.t * Scope.sig_state * Proof.t * proof_finalizer

let current_goals : proof_state -> Proof.Goal.t list = fun (_,_,p,_) ->
  p.proof_goals

type command_result =
  | Cmd_OK    of command_state
  | Cmd_Proof of proof_state * Tactic.t list * Pos.popt * Pos.popt
  | Cmd_Error of Pos.popt option * string

type tactic_result =
  | Tac_OK    of proof_state
  | Tac_Error of Pos.popt option * string

let t0 = Time.save ()

let initial_state : Files.module_path -> command_state = fun path ->
  Time.restore t0;
  Sign.loading := [path];
  let sign = Sign.create path in
  Sign.loaded  := Files.PathMap.add path sign !Sign.loaded;
  (Time.save (), Scope.empty_sig_state sign)

let handle_command : command_state -> Command.t -> command_result =
    fun (st,ss) cmd ->
  Time.restore st;
  try
    let (ss, pst) = Handle.handle_cmd ss cmd in
    let t = Time.save () in
    match pst with
    | None       -> Cmd_OK(t, ss)
    | Some(data) ->
        let pst = (t, ss, data.pdata_p_state, data.pdata_finalize) in
        let ts = data.pdata_tactics in
        Cmd_Proof(pst, ts, data.pdata_stmt_pos, data.pdata_term_pos)
  with Fatal(p,m) -> Cmd_Error(p,m)

let handle_tactic : proof_state -> Tactic.t -> tactic_result = fun s t ->
  let (_, ss, p, finalize) = s in
  try
    let p = Tactics.handle_tactic ss p t in
    Tac_OK(Time.save (), ss, p, finalize)
  with Fatal(p,m) -> Tac_Error(p,m)

let end_proof : proof_state -> command_result = fun s ->
  let (_, ss, p, finalize) = s in
  try Cmd_OK(Time.save (), finalize ss p) with Fatal(p,m) -> Cmd_Error(p,m)

let get_symbols : command_state -> (Terms.sym * Pos.popt) StrMap.t = fun s ->
  Time.restore (fst s);
  !(Sign.((current_sign ()).sign_symbols))

(* Equality on *)
let%test _ =
  let c = parse_text "foo.lp" "symbol const B : TYPE" in
  List.equal Command.equal c c

(* Equality not *)
let%test _ =
  let c = parse_text "foo.lp" "symbol const B : TYPE" in
  let d = parse_text "foo.lp" "symbol const C : TYPE" in
  not (List.equal Command.equal c d)

(* Equality is not sensitive to whitespace *)
let%test _ =
  let c = parse_text "foo.lp" "symbol   const  B : TYPE" in
  let d = parse_text "foo.lp" "  symbol const B :   TYPE " in
  List.equal Command.equal c d

(* More complex test stressing most commands *)
let%test _ =
  let c = parse_text "foo.lp" "
symbol const B : TYPE

symbol const true  : B
symbol const false : B
symbol bool_neg : B ⇒ B

rule bool_neg true  → false
rule bool_neg false → true

symbol const Prop : TYPE
symbol injective P : Prop ⇒ TYPE

symbol const eq : ∀a, T a ⇒ T a ⇒ Prop

theorem notK : ∀a, P (eq bool (bool_neg (bool_neg a)) a)
proof
   intro a
qed
" in
  List.equal Command.equal c c

