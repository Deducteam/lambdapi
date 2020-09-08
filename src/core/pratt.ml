(** A simple parser for operators. See Pratt parsing or the Shunting Yard
    algorithm.

    <https://dev.to/jrop/pratt-parsing>
    <https://effbot.org/zone/simple-top-down-parsing.htm> *)

open Syntax
open Extra

module Pratt : sig
  val expression : ?rbp:priority -> p_term Stream.t -> p_term
end = struct
  (** [lbp t] returns the binding power of term [t] (which is 0 if [t] is not
      an operator). *)
  let lbp : p_term -> priority = fun {elt=t; _} ->
    match t with
    | P_Iden({elt=(_,s); _}, _) ->
        begin match StrHtbl.find_opt bin_operators s with
          | Some(_, _, bp, _) -> bp
          | None ->
              begin match StrHtbl.find_opt una_operators s with
                | Some(_, bp, _) -> bp
                | None -> 0.
              end
        end
    | _ -> 0.

  (** [nud t] is the production of term [t] with {b no} left context. If [t]
      is not an operator, [nud] is the identity. Otherwise, the output is a
      production rule. *)
  let rec nud : p_term Stream.t -> p_term -> p_term = fun strm t ->
    match t.elt with
    | P_Iden({elt = (_, s); pos}, _) ->
        begin match StrHtbl.find_opt una_operators s with
          | None -> t
          | Some((_, rbp, _) as op) ->
              Pos.make pos (P_UnaO(op, expression ~rbp strm))
        end
    | _ -> t

  (** [led left t] is the production of operator [op] with left context
      [left]. *)
  and led : p_term Stream.t -> p_term -> p_term -> p_term = fun strm left t ->
    match t.elt with
    | P_Iden({elt = (_, s); pos}, _) ->
        begin match StrHtbl.find_opt bin_operators s with
          | None -> t
          | Some((_, assoc, bp, _) as op) ->
              let rbp =
                if assoc = Assoc_right then bp -. epsilon_float else bp
              in
              (* REVIEW: and for non associative? *)
              Pos.make pos (P_BinO(left, op, expression ~rbp strm))
        end
    | _ -> t

  (** [expression rbp s] parses stream of tokens [s] with right binding power
      [rbp]. It transforms a sequence of applications to a structured
      application tree containing infix and prefix operators. For instance,
      assuming that [+] is declared infix, it transforms [3 + 5 + 2],
      represented as [@(@(@(@(3,+),5),+),2)] (where [@] is the application)
      into [(@(+(@(+,3,5)),2)]. Note that it doesn't recurse into terms such
      as abstractions or arrows. *)
  and expression : ?rbp:priority -> p_term Stream.t -> p_term =
    fun ?(rbp = 0.) strm ->
    let rec aux left =
      match Stream.peek strm with
      | None -> left
      | Some(pt) ->
          if lbp pt > rbp then
            (* Performed before to execute side effect on stream. *)
            let next = Stream.next strm in
            aux (led strm left next) else
           left
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