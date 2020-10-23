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

(** [sanity_check pos s] checks that the token [s] is appropriate for an
    infix operator or a declared identifier. If it is not the case, then the
    [Fatal] exception is raised. *)
(* REVIEW: this function might be removed since operators are now regular
   identifiers. *)
let sanity_check : Pos.pos -> string -> unit = fun loc s ->
  (* Of course, the empty string and keywords are forbidden. *)
  if s = "" then parser_fatal loc "Invalid token (empty).";
  if is_keyword s then
    parser_fatal loc "Invalid token (reserved).";
  (* Special case for debug flags *)
  if Lp_lexer.is_debug_flag s then
    parser_fatal loc "Invalid token (is a debug flag).";
  (* We also reject symbols with certain substrings. *)
  let check_substring w =
    if String.is_substring w s then
      parser_fatal loc "Invalid token (has [%s] as a substring)." w
  in
  List.iter check_substring forbidden_in_ops
