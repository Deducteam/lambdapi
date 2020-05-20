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
  let ids = Proof.get_names g in
  let term = term_in ids in
  let env_elt (s,(_,t,d)) =
    let t = to_string term t in
    s,
    match d with
    | None -> t
    | Some d -> t^" ≔ "^to_string term d
  in
  let ctx_elt (x,a,d) =
    let a = to_string term a in
    to_string var x,
    match d with
    | None -> a
    | Some d -> a^" ≔ "^to_string term d
  in
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

(* Equality on *)
let test_file = "./tests/foo.lp"
let debug_test = false

let log =
  if debug_test then
    begin
      Format.eprintf "@[";
      (* Format.eprintf "@[%s %s %-10s: @[" (level_to_string level) (comp_to_string component) (L.tostring loc); *)
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@\n%!") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let pp_pos fmt (c : Command.t) =
  Format.fprintf fmt "%a" Pos.pp (Command.get_pos c)

(* Equality is reflexive *)
let%test _ =
  let (c,_) = parse_text ~fname:test_file "constant symbol B : TYPE;" in
  List.equal Command.equal c c

(* Equality not *)
let test_command_eq cmd1 cmd2 =
  let (c,r_c) = parse_text ~fname:test_file cmd1 in
  let (d,r_d) = parse_text ~fname:test_file cmd2 in
  match r_c, r_d with
  | None, None ->
    List.equal Command.equal c d
  | _, _ ->
    log "error happened in test_command_eq: parsing error";
    false

let%test _ =
  let c1 = "constant symbol B : TYPE;" in
  let c2 = "constant symbol C : TYPE;" in
  not (test_command_eq c1 c2)

(* Equality is not sensitive to whitespace *)
let%test _ =
  let c1 = "constant   symbol  B : TYPE;"  in
  let c2 = " constant symbol B :   TYPE; " in
  test_command_eq c1 c2

(* More complex tests stressing most commands *)

(* Equality is reflexive *)
let%test _ =
  let (c,_) = parse_text ~fname:test_file
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
  List.equal Command.equal c c

(* TODO *)

(* test: Check that parsing from the file is the same that parsing from string *)
(* Equality is reflexive *)
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

let (let+) x f = Result.map f x
let (let*) = Result.bind

let pp_lexpos fmt
  { Lexing.pos_fname
  ; pos_lnum
  ; pos_bol
  ; pos_cnum
  } =
  Format.fprintf fmt "file: %s; pos_lnum = %d; pos_bol = %d; pos_cnum = %d"
    pos_fname pos_lnum pos_bol pos_cnum

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
    let p = Parser.parse_from_lexbuf pa in
    parse_command p
end

(* auxiliary function *)
let parse_with_pos ~fname pos cmd_l =
  let rec aux pos cmd_l acc =
    match cmd_l with
    | [] -> Result.Ok (List.rev acc)
    | t :: cmd_l ->
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

let parse_split input =
  let debug = false in
  let input_split = String.split_on_char ';' input in
  let input_split = List.map (fun s -> s ^ ";") input_split in
  let input_split = List.(list_take (length input_split - 1)) input_split in
  if debug then Format.eprintf "input_split: @[%a@]@\n" Format.(pp_print_list pp_print_string) input_split;
  let cmds_1, _ = parse_text ~fname:test_file input in
  match parse_with_pos ~fname:test_file (Parsing.zero_pos test_file) input_split with
  | Error err ->
    (* log "error in parse_with_pos %s" err; *)
    false
  | Ok cmds_2 ->
    if debug then Format.eprintf "pos for 1: @[%a@]@\n" Format.(pp_print_list pp_pos) cmds_1;
    if debug then Format.eprintf "pos for 2: @[%a@]@\n" Format.(pp_print_list pp_pos) cmds_2;
    (* Ideally we'd like to have better eq functions *)
    List.equal (=) cmds_1 cmds_2
   (* List.equal Command.equal cmds_1 cmds_2 *)

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

(* Test for notation: check that parsing with notation is correct and that fails when not present *)

(* Test for positions: check that the positions are correct, including when we
   resume parsing from the middle of the file *)
