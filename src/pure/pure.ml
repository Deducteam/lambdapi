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
  (* TODO: Fixme not to use generic equality *)
  let equal_with_pos = (=)
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

let parse_command p : (Command.t, Pos.popt * string) Result.t =
  match Stream.peek p with
  | None ->
    Result.Error (None, "EOF")
  | Some c ->
    Ok c
  | exception Fatal(Some(Some(pos)), msg) ->
    Error(Some pos, msg)
  | exception Fatal(Some(None)     , _  ) ->
    assert false
  | exception Fatal(None           , _  ) ->
    assert false

(** Exception raised by [parse_text] on error. *)

let parse_text :
      fname:string -> string -> Command.t list * (Pos.pos * string) option =
  fun ~fname s ->
  let parse_string =
    if Filename.check_suffix fname dk_src_extension then
      Parser.Dk.parse_string
    else Parser.parse_string
  in
  let cmds = Stdlib.ref [] in
  try
    Stream.iter (fun c -> Stdlib.(cmds := c :: !cmds)) (parse_string fname s);
    List.rev Stdlib.(!cmds), None
  with
  | Fatal(Some(Some(pos)), msg) -> List.rev Stdlib.(!cmds), Some(pos, msg)
  | Fatal(Some(None)     , _  ) -> assert false
  | Fatal(None           , _  ) -> assert false

let parse_file :
      fname:string -> Command.t list * (Pos.pos * string) option =
  fun ~fname ->
  let parse_file =
    if Filename.check_suffix fname dk_src_extension then
      Parser.Dk.parse_file
    else Parser.parse_file
  in
  let cmds = Stdlib.ref [] in
  try
    Stream.iter (fun c -> Stdlib.(cmds := c :: !cmds)) (parse_file fname);
    List.rev Stdlib.(!cmds), None
  with
  | Fatal(Some(Some(pos)), msg) -> List.rev Stdlib.(!cmds), Some(pos, msg)
  | Fatal(Some(None)     , _  ) -> assert false
  | Fatal(None           , _  ) -> assert false

type proof_finalizer = Sig_state.t -> Proof.proof_state -> Sig_state.t

type proof_state =
  Time.t * Sig_state.t * Proof.proof_state * proof_finalizer * bool * Pos.popt

let current_goals : proof_state -> Goal.info list =
  fun (time, st, ps, _, _, _) ->
  Time.restore time;
  Print.sig_state := st;
  List.map Goal.to_info ps.proof_goals

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
  let sign = Sign.create mp in
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
    Cmd_Error(Some p, Pos.popt_to_string p ^ " " ^ m)

let handle_tactic : proof_state -> Tactic.t -> int -> tactic_result =
  fun (_, ss, ps, finalize, prv, sym_pos) tac n ->
  try
    let ps, qres = Handle.Tactic.handle ss sym_pos prv (ps, None) tac n in
    let qres = Option.map (fun f -> f ()) qres in
    Tac_OK((Time.save (), ss, ps, finalize, prv, sym_pos), qres)
  with Fatal(Some p,m) ->
    Tac_Error(Some p, Pos.popt_to_string p ^ " " ^ m)

let end_proof : proof_state -> command_result =
  fun (_, ss, ps, finalize, _, _) ->
  try Cmd_OK((Time.save (), finalize ss ps), None)
  with Fatal(Some p,m) ->
    Cmd_Error(Some p, Pos.popt_to_string p ^ " " ^ m)

let get_symbols : state -> Term.sym Extra.StrMap.t =
  fun (_, ss) -> ss.in_scope

(* Equality tests, important for the incremental engine *)

(* There are two kind of tests for equality:

   - tests that ignore the positions inside the Ast: these are important for
   "semantic" equality

   - tests that need to compare terms including positions: important to see
   parsing resumption works correctly
*)

let test_file = "./tests/foo.lp"

module TestUtil = struct
  let debug_test = false

  (* Log combinator *)
  let log =
    if debug_test then
      begin
        Format.eprintf "@[";
        (* Format.eprintf "@[%s %s %-10s: @["
           (level_to_string level) (comp_to_string component)
           (L.tostring loc); *)
        Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@\n%!")
          Format.err_formatter
      end
    else
      Format.ifprintf Format.err_formatter

  (* Test combinator *)
  let test_command_eq eq cmd1 cmd2 =
    let (c,r_c) = parse_text ~fname:test_file cmd1 in
    let (d,r_d) = parse_text ~fname:test_file cmd2 in
    match r_c, r_d with
    | None, None ->
      List.equal eq c d
    | _, _ ->
      log "error happened in test_command_eq: parsing error";
      false

  let pp_pos fmt (c : Command.t) =
    Format.fprintf fmt "%a" Pos.pp (Command.get_pos c)

  let pp_cmd_list_pos fmt (c : Command.t list) =
    Format.(fprintf fmt "@[%a@]" (pp_print_list pp_pos) c)

  let pp_lexpos fmt
      { Lexing.pos_fname
      ; pos_lnum
      ; pos_bol
      ; pos_cnum
      } =
    Format.fprintf fmt "file: %s; pos_lnum = %d; pos_bol = %d; pos_cnum = %d"
      pos_fname pos_lnum pos_bol pos_cnum

end

(* Test: equality is reflexive *)
let%test _ =
  let (c,_) = parse_text ~fname:test_file "constant symbol B : TYPE;" in
  List.equal Command.equal c c

let%test _ =
  let c1 = "constant symbol B : TYPE;" in
  let c2 = "constant symbol C : TYPE;" in
  not (TestUtil.test_command_eq Command.equal c1 c2)

(* Equality is not sensitive to whitespace *)
let%test _ =
  let c1 = "constant   symbol  B : TYPE;"  in
  let c2 = " constant symbol B :   TYPE; " in
  TestUtil.test_command_eq Command.equal c1 c2

(* Equality with positions is sensitive to whitespace *)
let%test _ =
  let c1 = "constant   symbol  B : TYPE;"  in
  let c2 = " constant symbol B :   TYPE; " in
  not (TestUtil.test_command_eq Command.equal_with_pos c1 c2)

(* More complex tests stressing most commands *)

(* Equality is reflexive *)
let%test _ =
  let (c,_) = parse_text ~fname:test_file
      (* copied from src/pure/tests/foo.lp. keep in sync. *)
      "constant symbol B : TYPE;

constant symbol true  : B;
constant symbol false : B;

symbol neg : B → B;

rule neg true  ↪ false;
rule neg false ↪ true;

constant symbol Prop : TYPE;

injective symbol P : Prop → TYPE;

constant symbol eq : B → B → Prop;
constant symbol refl b : P (eq b b);

constant symbol case (p : B → Prop) : P (p true) → P (p false) → Π b, P b;

opaque symbol notK : Π b, P (eq (neg (neg b)) b)
≔ begin
  assume b;
  apply case (λ b, eq (neg (neg b)) b)
  {apply refl}
  {apply refl}
end;
" in
  List.equal Command.equal c c

(* Equality is reflexive, when reading from a file *)
let%test _ =
  let (c_file, _) = parse_file ~fname:test_file in
  let (c_string,_) = parse_text ~fname:test_file
      (* copied from tests/OK/foo.lp. keep in sync. *)
"constant symbol B : TYPE;

constant symbol true  : B;
constant symbol false : B;

symbol neg : B → B;

rule neg true  ↪ false;
rule neg false ↪ true;

constant symbol Prop : TYPE;

injective symbol P : Prop → TYPE;

constant symbol eq : B → B → Prop;
constant symbol refl b : P (eq b b);

constant symbol case (p : B → Prop) : P (p true) → P (p false) → Π b, P b;

opaque symbol notK : Π b, P (eq (neg (neg b)) b)
≔ begin
  assume b;
  apply case (λ b, eq (neg (neg b)) b)
  {apply refl}
  {apply refl}
end;
" in
  List.equal Command.equal c_string c_file

(* test: Check that parsing commutes *)

(* New parsing API for Flèche / LP-LSP *)
module Parsing : sig
  type t

  val make : pos:Lexing.position -> string -> t
  val loc : t -> Lexing.position
  val zero_pos : string -> Lexing.position
  val parse : t -> (Command.t, Pos.popt * string) Result.t

end = struct

  type t = Sedlexing.lexbuf

  (* Zero position *)
  let zero_pos pos_fname =
    { Lexing.pos_fname
    ; pos_lnum = 1
    ; pos_bol = 0
    ; pos_cnum = 0
    }

  let make ~pos t =
    let lexbuf = Sedlexing.Utf8.from_string t in
    Sedlexing.set_position lexbuf pos;
    Sedlexing.set_filename lexbuf pos.pos_fname;
    lexbuf

  let loc pa = Sedlexing.lexing_position_curr pa

  let parse pa =
    let p = Parser.parse_lexbuf pa in
    parse_command p
end

(* auxiliary function *)
let parse_with_pos ~fname pos cmd_l =
  let rec aux pos cmd_l acc =
    match cmd_l with
    | [] -> Result.Ok (List.rev acc)
    | t :: cmd_l ->
      let (let*) = Result.bind in
      let pa = Parsing.make ~pos t in
      let* c = Parsing.parse pa in
      let pos = Parsing.loc pa in
      aux pos cmd_l (c :: acc)
  in
  aux pos cmd_l []

(* List.take only supported in 5.3, we ship a copy here *)
let list_take n l =
  let[@tail_mod_cons] rec aux n l =
    match n, l with
    | 0, _ | _, [] -> []
    | n, x::l -> x::aux (n - 1) l
  in
  if n < 0 then invalid_arg "List.take";
  aux n l

(* this function tries to split a set of sentences using a heuristic, then
   compares, including positions! *)
let parse_split input =
  let debug = false in
  let input_split = String.split_on_char ';' input in
  let input_split = List.map (fun s -> s ^ ";") input_split in
  let input_split = List.(list_take (length input_split - 1)) input_split in
  if debug then
    Format.eprintf "input_split: @[%a@]@\n"
      Format.(pp_print_list pp_print_string) input_split;
  let cmds_1, _ = parse_text ~fname:test_file input in
  match parse_with_pos ~fname:test_file (Parsing.zero_pos test_file)
          input_split with
  | Error err ->
    (* log "error in parse_with_pos %s" err; *)
    false
  | Ok cmds_2 ->
      if debug then
        Format.eprintf "pos for 1: @[%a@]@\npos for 2: @[%a@]@\n"
          TestUtil.pp_cmd_list_pos cmds_1 TestUtil.pp_cmd_list_pos cmds_2;
      (* Here, we compare with positions *)
      List.equal Command.equal_with_pos cmds_1 cmds_2

let%test _ =
  let input = "
constant symbol B : TYPE;
constant symbol C : TYPE;
constant symbol D : TYPE;
constant symbol E : TYPE;
constant symbol F : TYPE;
" in
  parse_split input

let%test _ =
  let input =
"constant symbol B : TYPE;

constant symbol true  : B;
constant symbol false : B;

symbol neg : B → B;

rule neg true  ↪ false;
rule neg false ↪ true;

constant symbol Prop : TYPE;

injective symbol P : Prop → TYPE;

constant symbol eq : B → B → Prop;
constant symbol refl b : P (eq b b);

constant symbol case (p : B → Prop) : P (p true) → P (p false) → Π b, P b;

" in
  parse_split input

(* TODO test for notation: check that parsing with notation is correct and
   that fails when not present *)

(* TODO test for positions: check that the positions are correct, including
   when we resume parsing from the middle of the file *)
