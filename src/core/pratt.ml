(** This module defines functions needed by the Pratt parser of the Pratter
    library. *)

open Syntax

module Pratt : sig
  val parse : Sig_state.t -> Env.t -> p_term -> p_term
end = struct

  open Lplib
  open Extra
  open Pos

  (** [find_qid ss env qid] fetches the qualified identifier associated to
      [qid] if [qid] is the identifier of an infix operator defined in
      signature state [ss]. If [qid] is defined in environment [env], then it
      designates a variable, and is thus returned as-is. *)
  (* REVIEW: this function relies on a lot of invariants and performs many
     [Map.find_opt]s. Things may be optimised by modifying the data structure
     of the signature state, notably making the qualified identfier to which
     operators are linked available in the [unops] field of the signature
     state. *)
  let find_qid : Sig_state.t -> Env.t -> qident -> qident =
    fun ss env ({elt=(mp, s); _} as qid) ->
    try
      if mp <> [] then raise Not_found;
      ignore (Env.find s env);
      qid
    with Not_found ->
    match StrMap.find_opt s ss.Sig_state.unops with
    | Some sym -> (
        match Terms.SymMap.find_opt sym ss.Sig_state.pp_hints with
        | Some (Prefix(_, _, qid)) -> qid
        | _ -> assert false )
    | None -> (
        match StrMap.find_opt s ss.Sig_state.binops with
        | Some sym -> (
            match Terms.SymMap.find_opt sym ss.Sig_state.pp_hints with
            | Some (Infix (_, _, _, qid)) -> qid
            | _ -> assert false )
        | None -> qid )


  module Pratt_terms : Pratter.SUPPORT
    with type term = p_term
     and type table = Sig_state.t * Env.t
  = struct
    type term = p_term
    type table = Sig_state.t * Env.t

    let get_binary (tbl, _) t =
      let open Sig_state in
      match t.elt with
      | P_Iden(id, _) -> (
          let {elt=(_, suffix); _} = id in
          match StrMap.find_opt suffix tbl.binops with
          | None -> None
          | Some(sym) ->
          match Terms.SymMap.find_opt sym tbl.pp_hints with
          | Some(Infix((_, assoc, prio, _))) -> (
              let assoc =
                match assoc with
                | Assoc_left -> Pratter.Left
                | Assoc_right -> Pratter.Right
                | Assoc_none -> assert false
              in
              Some(prio,assoc))
          | _ -> None )
      | _ -> None

    let get_unary (tbl, _) t =
      let open Sig_state in
      match t.elt with
      | P_Iden(id, _) -> (
          let {elt=(_, suffix); _} = id in
          match StrMap.find_opt suffix tbl.unops with
          | None -> None
          | Some(sym) ->
          match Terms.SymMap.find_opt sym tbl.pp_hints with
          | Some(Prefix((_, prio, _))) -> Some(prio)
          | _ -> None )
      | _ -> None

    let make_appl (tbl, env) t u =
      let pos =
        match t.pos, u.pos with
        | Some(pt), Some(pu) -> Some(cat pt pu)
        | None, _ | _, None -> None
      in
      let t =
        make t.pos
          (match t.elt with
           | P_Iden(qid, b) -> P_Iden(find_qid tbl env qid, b)
           | _ -> t.elt)
      in
      let u =
        make u.pos
          (match u.elt with
           | P_Iden(qid, b) -> P_Iden(find_qid tbl env qid, b)
           | _ -> u.elt)
      in
      make pos (P_Appl(t, u))
  end

  (** [parse t] Pratt parses applications in term [t]. Note that it doesn't
      recurse into abstractions or implications and alike. *)
  let parse : Sig_state.t -> Env.t -> p_term -> p_term = fun st env t ->
    let (h,args) = Syntax.p_get_args t in
    let strm = Stream.of_list (h::args) in
    let module Parse = Pratter.Make(Pratt_terms) in
    Parse.expression (st, env) strm
end
include Pratt
