type 'token lexbuf
val new_parser :
  pp:(Format.formatter -> 'token -> unit) ->
  lexer_:(unit -> 'token * Lexing.position * Lexing.position) ->
  'token lexbuf
val current_token : 'token lexbuf -> 'token
val current_pos : 'token lexbuf -> Lexing.position * Lexing.position
val consume_token : 'token lexbuf -> unit
val succeed_or_reset_stream : ('token lexbuf -> 'a) -> 'token lexbuf -> 'a
