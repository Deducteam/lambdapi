(** A simple parser for operators. See Pratt parsing or the Shunting Yard
    algorithm.

    <https://dev.to/jrop/pratt-parsing>
    <https://effbot.org/zone/simple-top-down-parsing.htm> *)

open Syntax

module Pratt : sig
  val parse : Sig_state.t -> p_term -> p_term
end = struct

  open Lplib
  open Extra
  open Pos

  module Pratt_terms : Pratter.SUPPORT
    with type term = p_term
     and type table = Sig_state.t
  = struct
    type term = p_term
    type table = Sig_state.t

    let get_binary tbl t =
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

    let get_unary tbl t =
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

    let make_appl tbl t u =
      let pos =
        match t.pos, u.pos with
        | Some(pt), Some(pu) -> Some(cat pt pu)
        | None, _ | _, None -> None
      in
      let find_qid {elt; pos} =
        match elt with
        | P_Iden(qid, _) -> (
            match StrMap.find_opt (snd qid.elt) tbl.Sig_state.unops with
            | Some(sym) ->
              let path = List.map (fun p -> (p, true)) sym.Terms.sym_path in
              Some(make pos (path, sym.Terms.sym_name))
            | None -> (
                match StrMap.find_opt (snd qid.elt) tbl.Sig_state.binops with
                | Some sym ->
                    let path =
                      List.map (fun p -> (p, true)) sym.Terms.sym_path
                    in
                  Some(make pos (path, sym.Terms.sym_name))
                | None -> Some(qid)
              )
          )
        | _ -> None
      in
      let t =
        match find_qid t with
        | Some(qid) -> make t.pos (P_Iden(qid, false))
        | None -> t
      in
      let u =
        match find_qid u with
        | Some(qid) -> make t.pos (P_Iden(qid, false))
        | None -> u
      in
      make pos (P_Appl(t, u))
  end

  (** [parse t] Pratt parses applications in term [t]. Note that it doesn't
      recurse into abstractions or implications and alike. *)
  let parse : Sig_state.t -> p_term -> p_term = fun st t ->
    let (h,args) = Syntax.p_get_args t in
    let strm = Stream.of_list (h::args) in
    let module Parse = Pratter.Make(Pratt_terms) in
    Parse.expression st strm
end
include Pratt
