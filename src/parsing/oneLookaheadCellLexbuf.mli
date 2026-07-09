type 'token lexbuf
val new_parser :
  pp:(Format.formatter -> 'token -> unit) ->
  lexer_:(unit -> 'token * Lexing.position * Lexing.position) ->
  'token lexbuf
val current_token : 'token lexbuf -> 'token
val current_pos : 'token lexbuf -> Lexing.position * Lexing.position
val consume_token : 'token lexbuf -> unit
val add_expected_tokens: 'token lexbuf -> 'token list -> unit
(** Record tokens that would have been accepted at the current
    lookahead token. Recordings accumulate until the next
    [consume_token], which clears them. *)

val get_expected_tokens: 'token lexbuf -> 'token list
