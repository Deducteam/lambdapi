(** Some functions for the parser. *)
open Lplib

(** [parser_fatal loc fmt] is a wrapper for [Console.fatal] that enforces that
    the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) Console.koutfmt -> 'a = fun loc fmt ->
  Console.fatal (Some(loc)) fmt

let is_keyword : string -> bool = fun s ->
  List.mem s
    ["as"; "in"; "TYPE"; "let"] (* TODO: finish *)

(** The following should not appear as substrings of binary operators, as they
    would introduce ambiguity in the parsing. *)
let forbidden_in_ops =
  [ "("; ")"; "."; "λ"; "Π"; "$"; "["; "]"; "{"; "}"; "?"; ":"; "↪"; "⊢"
  ; "→"; "@"; ","; ";"; "\""; "\'"; "≔"; "//"; " "; "\r"; "\n"; "\t"; "\b"
  ; "/*" ]
  @ List.init 10 string_of_int
