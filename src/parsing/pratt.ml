(** Parsing of infix operators using the Pratter library.

    The interface for the Pratter library can be seen at
    @see <https://forge.tedomum.net/koizel/pratter>. *)

open Common
open Core
open Syntax

module Pratt : sig
  val parse : ?find_sym:Sig_state.find_sym -> Sig_state.t -> Env.t
              -> p_term -> p_term
  (** [parse ~find_sym ss env t] Pratt parses term [t], unsugaring infix
      operators and prefix operators using signature state [ss] and
      environment [env] to determine which term is an operator, and to build
      new terms. Note that it doesn't recurse into abstractions or
      implications and alike. [~find_sym] is used to scope symbol
      identifiers. *)
end = struct

  open Lplib
  open Pos

  let is_op : Sig_state.find_sym -> Sig_state.t -> Env.t -> p_term
              -> (Pratter.fixity * float) option =
   fun find_sym ss env t ->
     match t.elt with
     | P_Iden({elt=(mp, s); _} as id, false) ->
         let open Option.Monad in
         let* sym =
           try (* Look if [id] is in [env]... *)
             if mp <> [] then raise Not_found;
             ignore (Env.find s env); None
           with Not_found -> (* ... or look into the signature *)
             Some(find_sym ~prt:true ~prv:true ss id)
         in
         (match Timed.(!(sym.sym_not)) with
         | Term.Infix(assoc, prio) -> Some(Pratter.Infix assoc, prio)
         | Term.Prefix(prio) | Succ(Prefix(prio)) ->
             Some(Pratter.Prefix, prio)
         | Term.Postfix(prio) | Succ(Postfix(prio)) ->
             Some(Pratter.Postfix, prio)
         | _ -> None)
     | _ -> None

   let appl : p_term -> p_term -> p_term = fun t u ->
     Pos.make (Pos.cat t.pos u.pos) (P_Appl(t, u))

  (* NOTE the term is converted from appl nodes to list in [Pratt.parse],
   rebuilt into appl nodes by [Pratt.parse], and then decomposed again into a
   list by [get_args]. We could make [Pratt.parse] return a list of terms
   instead. *)
  let parse : ?find_sym:Sig_state.find_sym ->
    Sig_state.t -> Env.t -> p_term -> p_term =
    fun ?(find_sym=Sig_state.find_sym) st env t ->
    let h, args = Syntax.p_get_args t in
    let strm = Stream.of_list (h :: args) in
    let is_op = is_op find_sym st env in
    match Pratter.expression ~is_op ~appl strm with
    | Ok e -> e
    | Error `TooFewArguments ->
        Error.fatal t.pos "Malformed application in \"%a\"" Pretty.term t
    | Error `OpConflict (t, u) ->
        Error.fatal t.pos "Operator conflict between \"%a\" and \"%a\""
          Pretty.term t Pretty.term u
    | Error `UnexpectedInfix t ->
        Error.fatal t.pos "Unexpected infix operator \"%a\"" Pretty.term t
    | Error `UnexpectedPostfix t ->
        Error.fatal t.pos "Unexpected postfix operator \"%a\"" Pretty.term t
end
include Pratt
