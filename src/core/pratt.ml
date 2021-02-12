(** This module defines functions needed by the Pratt parser of the Pratter
    library.

    The interface for the Pratter library can be seen at
    @see <https://forge.tedomum.net/koizel/pratter> *)

open Common
open Parsing
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
      | P_Iden(id, _) -> (
          let sym =
            let {elt=(mp, s); _} = id in
            try (* Look if [id] is in [env]... *)
              if mp <> [] then raise Not_found;
              ignore (Env.find s env); None
            with Not_found -> (* ... or look into the signature *)
              Some(Sig_state.find_sym ~prt:true ~prv:true tbl id)
          in
          let f sym =
            match Term.SymMap.find_opt sym tbl.notations with
            | Some(Infix(_, assoc, prio, _)) -> Some(Pratter.Bin assoc, prio)
            | Some(Prefix(_, prio, _)) -> Some(Pratter.Una, prio)
            | _ -> None
          in
          Option.bind f sym )
      | _ -> None

    let make_appl t u =
      let pos = Option.(Infix.(pure cat <*> t.pos <*> u.pos)) in
      make pos (P_Appl(t, u))
  end

  let parse : Sig_state.t -> Env.t -> p_term -> p_term = fun st env t ->
    let (h,args) = Syntax.p_get_args t in
    let strm = Stream.of_list (h::args) in
    let module Parse = Pratter.Make(Pratt_terms) in
    try Parse.expression (st, env) strm with
    | Parse.OpConflict(t, u) ->
        Error.fatal t.pos "Operator conflict between \"%a\" and \"%a\""
          Pretty.term t Pretty.term u
    | Parse.TooFewArguments ->
        Error.fatal t.pos "Malformed application in \"%a\"" Pretty.term t
end
include Pratt
