(** Parsing of infix operators using the Pratter library.

    The interface for the Pratter library can be seen at
    @see <https://forge.tedomum.net/koizel/pratter>. *)

open Common
open Core
open Syntax

module Pratt : sig
  val parse : Sig_state.t -> Env.t -> p_term -> p_term
  (** [parse ss env t] Pratt parses term [t], unsugaring infix operators and
      prefix operators using signature state [ss] and environment [env] to
      determine which term is an operator, and to build new terms. Note that
      it doesn't recurse into abstractions or implications and alike. *)
end = struct

  open Lplib
  open Pos

  module Pratt_terms : Pratter.SUPPORT
    with type term = p_term
     and type table = Sig_state.t * Env.t
  = struct
    type term = p_term
    type table = Sig_state.t * Env.t

    (* Get properties of term [t] if its an operator. *)
    let get (tbl, env) t =
      match t.elt with
      | P_Iden({elt=(mp, s); _} as id, false) ->
          let sym =
            try (* Look if [id] is in [env]... *)
              if mp <> [] then raise Not_found;
              ignore (Env.find s env); None
            with Not_found -> (* ... or look into the signature *)
              Some(Sig_state.find_sym ~prt:true ~prv:true tbl id)
          in
          let f sym =
            match Term.SymMap.find_opt sym tbl.notations with
            | Some(Infix(assoc, prio)) -> Some(Pratter.Infix assoc, prio)
            | Some(Prefix(prio)) -> Some(Pratter.Prefix, prio)
            | _ -> None
          in
          Option.bind f sym
      | _ -> None

    let make_appl t u = Pos.make (Pos.cat t.pos u.pos) (P_Appl(t, u))
  end

  (* NOTE the term is converted from appl nodes to list in [Pratt.parse],
   rebuilt into appl nodes by [Pratt.parse], and then decomposed again into a
   list by [get_args]. We could make [Pratt.parse] return a list of terms
   instead. *)
  let parse : Sig_state.t -> Env.t -> p_term -> p_term = fun st env t ->
    let h, args = Syntax.p_get_args t in
    let strm = Stream.of_list (h :: args) in
    let module Parse = Pratter.Make(Pratt_terms) in
    match Parse.expression (st, env) strm with
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
