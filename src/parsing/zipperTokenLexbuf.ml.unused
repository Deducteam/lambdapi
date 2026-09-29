let log = Common.Logger.make 'b' "zlex" "zipper buffer lexing"
let log = log.pp

type 'token token_pos = 'token * Lexing.position * Lexing.position

type 'token zipper = 'token token_pos list list * 'token token_pos list
(* A zipper to represent the token (and its position) stream
      l1 :: ... ln :: [], tkps
   represents the stream
      List.rev (l1 @ ... @ ln) @ tkps @ the_yet_unread_stream
   where the current stream position is just before tkps,
   i.e. tkps are the next tokens to be consumed while
   (l1 @ ... @ ln) are tokens already consumed.

   consume_token moves the next token from tkps to the top of l1,
   it it exists

   an l1 is pushed on the stack of stacks of already consumed
   terms when succeed_or_reset_stream is called; in case of
   failures all tokens in l1 are moved back to tkps

   Invariants on a zipper z:
   - snd z is never empty: a token is fetch from the stream when
     consuming the last entry of snd z to maintain the invariant
   - fst z is empty iff we have not entered any
     succeed_or_reset_stream and thus the consumed tokens need not
     be preserved (the zipper functionality is deactivated).
     This is an optimization for performance reasons *)

type 'token lexbuf =
 { pp_token : (Format.formatter -> 'token -> unit)
 ; get_next_token : unit -> 'token token_pos
 ; mutable the_current_token_pos : 'token zipper
 ; mutable expected_tokens : 'token list
 }

let new_parser ~pp ~lexer_ =
 { pp_token = pp
 ; get_next_token = lexer_
 ; the_current_token_pos = ([],[lexer_ ()])
 ; expected_tokens = []
 }

let pp_token (lb : 'token lexbuf) = lb.pp_token
let get_next_token (lb : 'token lexbuf) = lb.get_next_token ()
let the_current_token_pos (lb : 'token lexbuf) : 'token zipper =
 lb.the_current_token_pos
let (:=) lb z = lb.the_current_token_pos <- z

let current_token_pos lb =
 match the_current_token_pos lb with
 | _, [] -> assert false
 | _, tkp::_ -> tkp

let current_token lb : 'token =
  let (t,_,_) = current_token_pos lb in t

let current_pos lb : Lexing.position * Lexing.position =
  let (_,p1,p2) = current_token_pos lb in (p1,p2)

let consume_token (lb:'token lexbuf) : unit =
 begin
  match the_current_token_pos lb with
  | _, [] -> assert false
  | [], [_] ->
     lb := [], [get_next_token lb]
  | l::ll, [x] ->
     lb := (x::l)::ll, [get_next_token lb]
  | [], _::tkps ->
     lb := [], tkps
  | l::ll, tkp::tkps ->
     lb := (tkp::l)::ll, tkps
 end ;
 lb.expected_tokens <- [];
 if Common.Logger.log_enabled() then
   let (t,p1,p2) = current_token_pos lb in
   let p = Common.Pos.locate (p1,p2) in
   log "read new token %a %a" Common.Pos.short (Some p) (pp_token lb) t

let succeed_or_reset_stream f lb =
 let ll,tkps = the_current_token_pos lb in
 lb := []::ll,tkps ;
 try
  let res = f lb in
  match the_current_token_pos lb with
  | [], _ -> assert false
  | _::[], tkps ->
     lb := [], tkps ;
     res
  | l1::l2::ll, tkps ->
     lb := (l1@l2)::ll, tkps ;
     res
 with
  LpLexer.SyntaxError (true,_) as e ->
   match the_current_token_pos lb with
   | [], _ -> assert false
   | l::ll, tkps ->
      lb := ll, List.rev l @ tkps ;
      raise e

let set_expected_tokens lb l =
 lb.expected_tokens <- l

let get_expected_tokens lb =
 lb.expected_tokens
