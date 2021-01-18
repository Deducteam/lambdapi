(** This module defines functions needed by the Pratt parser of the Pratter
    library.

    The interface for the Pratter library can be seen at
    @see <https://forge.tedomum.net/koizel/pratter> *)

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

  (** [find_op_qid ss env qid] fetches the qualified identifier associated to
      [qid] if [qid] is the identifier of an infix or prefix operator defined
      in signature state [ss]. If [qid] does not designate an operator, [None]
      is returned. *)
  let find_op_qid : Sig_state.t -> Env.t -> qident -> qident option =
    fun ss env ({elt=(mp, s); _} as qid) ->
    try
      if mp <> [] then raise Not_found;
      ignore (Env.find s env);
      None
    with Not_found ->
      let sym = Sig_state.find_sym ~prt:true ~prv:true true ss qid in
      let get_hint s = Terms.SymMap.find_opt s ss.Sig_state.pp_hints in
      let qid_of_hint hint =
        match hint with
        | Sig_state.Prefix(_,_,qid) | Sig_state.Infix(_,_,_,qid) -> Some qid
        | _ -> None
      in
      Option.(Infix.(pure sym >>= get_hint >>= qid_of_hint ))

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
            let qid = find_op_qid tbl env id in
            Option.map (Sig_state.find_sym ~prt:true ~prv:true false tbl) qid
          in
          let f sym =
            match Terms.SymMap.find_opt sym tbl.pp_hints with
            | Some(Infix(_, assoc, prio, _)) -> Some(Pratter.Bin assoc, prio)
            | Some(Prefix(_, prio, _)) -> Some (Pratter.Una, prio)
            | _ -> None
          in
          Option.bind f sym )
      | _ -> None

    (* [make_appl (tbl, env) t u] applies [t] to [u]. If [t] or [u] are
       operators, their [qid] is resolved. That is, if [+] has been declared
       to be [Nat.plus], then [Nat.plus] is returned in the application. *)
    let make_appl (tbl, env) t u =
      let pos = Option.(Infix.(pure cat <*> t.pos <*> u.pos)) in
      let build =
        let f e =
          match e with
          | P_Iden(qid, b) ->
            let qid =
              match find_op_qid tbl env qid with
              | Some(qid) -> qid
              | None -> qid
            in
            P_Iden(qid, b)
          | _ -> e
        in
        Pos.map f
      in
      let t = build t in
      let u = build u in
      make pos (P_Appl(t, u))
  end

  let parse : Sig_state.t -> Env.t -> p_term -> p_term = fun st env t ->
    let (h,args) = Syntax.p_get_args t in
    let strm = Stream.of_list (h::args) in
    let module Parse = Pratter.Make(Pratt_terms) in
    Parse.expression (st, env) strm
end
include Pratt
