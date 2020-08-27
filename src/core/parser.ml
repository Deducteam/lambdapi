open Syntax
open Pos

(** [parser_fatal loc fmt] is a wrapper for [Console.fatal] that enforces that
    the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) Console.koutfmt -> 'a = fun loc fmt ->
  Console.fatal (Some(loc)) fmt

(* TODO: move to right place *)
type prio = PFunc | PAtom | PAppl

(** [add_prefix p s] adds the prefix [p] at the beginning of the
    identifier [s]. *)
let add_prefix : string -> string -> string = fun p s ->
  let n = String.length s in
  if n >= 4 && s.[0] ='{' && s.[1] = '|' then
    "{|" ^ p ^ String.sub s 2 (n-4) ^ "|}"
  else
    p ^ s

let parse_file : string -> Syntax.ast = fun fname ->
  let inchan = open_in fname in
  let parse =
    MenhirLib.Convert.Simplified.traditional2revised Lp_parser.command
  in
  let lexbuf = Sedlexing.Utf8.from_channel inchan in
  Sedlexing.set_filename lexbuf fname;
  let lexer = Lp_lexer.lexer lexbuf in
  let cmds = ref [] in
  let res =
    try
      while true do
        let cmd = parse lexer in
        cmds := cmd :: !cmds;
      done;
      assert false (* Should raise end of file before *)
    with
    | End_of_file -> List.rev !cmds
    | Lp_parser.Error ->
        let loc = Sedlexing.lexing_positions lexbuf in
        let loc = Pos.locate loc in
        parser_fatal loc "Unexpected token [%s]."
          (Sedlexing.Utf8.lexeme lexbuf)
  in
  close_in inchan;
  res

let parse_string : string -> string -> Syntax.ast = fun _ _ -> assert false

let parse_qident : string -> (qident, pos) result = fun _ -> assert false

let do_require : _ -> _ -> unit = fun _ _ -> assert false
