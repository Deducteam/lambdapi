let log = Common.Logger.make 'b' "zlex" "one lookahead cell buffer lexing"
let log = log.pp

type 'token token_pos = 'token * Lexing.position * Lexing.position

type 'token lexbuf =
 { pp_token : (Format.formatter -> 'token -> unit)
 ; get_next_token : unit -> 'token token_pos
 ; mutable the_current_token_pos : 'token token_pos
 ; mutable expected_tokens : 'token list
 }

let new_parser ~pp ~lexer_ =
 { pp_token = pp
 ; get_next_token = lexer_
 ; the_current_token_pos = lexer_ ()
 ; expected_tokens = []
 }

let pp_token (lb : 'token lexbuf) = lb.pp_token
let get_next_token (lb : 'token lexbuf) = lb.get_next_token ()

let current_token lb : 'token =
  let (t,_,_) = lb.the_current_token_pos in t

let current_pos lb : Lexing.position * Lexing.position =
  let (_,p1,p2) = lb.the_current_token_pos in (p1,p2)

let consume_token (lb:'token lexbuf) : unit =
 lb.the_current_token_pos <- get_next_token lb ;
 lb.expected_tokens <- [] ;
 if Common.Logger.log_enabled() then
   let (t,p1,p2) = lb.the_current_token_pos in
   let p = Common.Pos.locate (p1,p2) in
   log "read new token %a %a" Common.Pos.short (Some p) (pp_token lb) t

(* The tokens recorded since the last [consume_token] all describe
   alternatives rejected at the same lookahead token, so they
   accumulate rather than replace each other. *)
let add_expected_tokens lb l =
 lb.expected_tokens <- l @ lb.expected_tokens

let get_expected_tokens lb =
 lb.expected_tokens
