(** A simple parser for operators. See Pratt parsing or the Shunting Yard
    algorithm.

    <https://dev.to/jrop/pratt-parsing>
    <https://effbot.org/zone/simple-top-down-parsing.htm> *)

open Lplib
open Lplib.Extra

open Syntax

(** Type of operators with additional data. *)
(* REVIEW: simplify the type into [Unary of float * assoc] and remove [unop]
   and [binop] *)
type operator =
  | Unary of unop
  | Binary of binop

(** Table containing all registered binary and unary operators that may appear
    in terms parsed by {!val:Pratt.expression}. *)
let operators : operator StrHtbl.t = StrHtbl.create 17

module Pratt : sig
  val expression : ?rbp:priority -> p_term Stream.t -> p_term
  (** [expression rbp s] parses stream of tokens [s] with right binding power
      [rbp]. It transforms a sequence of applications to a structured
      application tree containing infix and prefix operators. For instance,
      assuming that [+] is declared infix, it transforms [3 + 5 + 2],
      represented as [@(@(@(@(3,+),5),+),2)] (where [@] is the application)
      into [(@(+(@(+,3,5)),2)]. Note that it doesn't recurse into terms such
      as abstractions or arrows. *)
end = struct

  (** [get_ident t] extracts a string and a position from [t] if it is an
      identifier. *)
  let get_ident : p_term -> (string * Pos.popt) option = fun {elt; pos} ->
    match elt with
    | P_Iden({elt=(_,s); _}, _) -> Some(s, pos)
    | _ -> None

  (** [lbp t] returns the left binding power of term [t] (which is 0 if [t] is
      not an operator). *)
  let lbp : p_term -> priority = fun pt ->
    match get_ident pt with
    | Some(s,_) ->
        begin match StrHtbl.find_opt operators s with
          | Some (Binary(_, _, bp, _))
          | Some (Unary(_, bp, _)) -> bp
          | None -> assert false
        end
    | _ -> assert false (* [t] must be an operator *)

  (* NOTE: among the four functions operating on streams, only [expression]
     consumes elements from it. *)

  (** [is_binop t] returns [true] iff term [t] is a binary operator. *)
  let is_binop : p_term -> bool = fun t ->
    match get_ident t with
    | Some(s,_) -> (
        match StrHtbl.find_opt operators s with
        | Some(Binary(_)) -> true
        | _ -> false )
    | _ -> false

  (** [nud t] is the production of term [t] with {b no} left context. If [t]
      is not an operator, [nud] is the identity. Otherwise, the output is a
      production rule. *)
  let rec nud : p_term Stream.t -> p_term -> p_term = fun strm t ->
    match get_ident t with
    | Some(s,p) ->
        begin match StrHtbl.find_opt operators s with
          | Some(Unary((_, rbp, _) as op)) ->
              Pos.make p (P_UnaO(op, expression ~rbp strm))
          | _ -> t
        end
    | _ -> t

  (** [led left t] is the production of term [t] with left context
      [left]. *)
  and led : p_term Stream.t -> p_term -> p_term -> p_term = fun strm left t ->
    match get_ident t with
    | Some(s,p) ->
        begin match StrHtbl.find_opt operators s with
          | Some(Binary((_, assoc, bp, _) as op)) ->
              let rbp =
                if assoc = Assoc_right then
                  bp *. (1. -. epsilon_float)
                else bp
              in
              (* REVIEW: and for non associative? *)
              Pos.make p (P_BinO(left, op, expression ~rbp strm))
          | _ -> assert false (* [t] must be an operator. *)
        end
    | _ -> assert false (* [t] must be an operator. *)

  and expression : ?rbp:priority -> p_term Stream.t -> p_term =
    fun ?(rbp = 0.) strm ->
    (* [aux left] inspects the stream and may consume one of its elements, or
       return [left] unchanged. *)
    let rec aux left =
      match Stream.peek strm with
      | None -> left
      | Some(pt) when is_binop pt ->
          (* If [pt] has a higher left binding power than the binding power of
             the previous operator in the stream. *)
          if lbp pt > rbp then
            (* Performed before to execute side effect on stream. *)
            let next = Stream.next strm in
            aux (led strm left next)
          else
            left
      | Some(_) -> (* argument of an application *)
          let next = Stream.next strm in
          let right = nud strm next in
          let pos =
            let open Lplib.Option.Infix in
            Pos.(Option.pure cat <*> next.pos <*> right.pos) in
          aux (Pos.make pos (P_Appl(left, right)))

    in
    let next = Stream.next strm in
    let left = nud strm next in
    aux left

end
include Pratt

(** [parse t] Pratt parses applications in term [t]. Note that it doesn't
    recurse into abstractions or implications and alike. *)
let parse : p_term -> p_term = fun t ->
  let (h,args) = Syntax.p_get_args t in
  let strm = Stream.of_list (h::args) in
  expression strm
