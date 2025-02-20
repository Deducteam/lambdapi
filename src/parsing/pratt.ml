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

   let ops (find_sym: Sig_state.find_sym) (ss: Sig_state.t) (env: Env.t)
     (t: p_term) : (Pratter.fixity * float * p_term) list =
     match t.elt with
     | P_Iden({elt=(mp, s); _} as id, false) ->
         let sym =
           try (* Look if [id] is in [env]... *)
             if mp <> [] then raise Not_found;
             ignore (Env.find s env); []
           with Not_found -> (* ... or look into the signature *)
             [find_sym ~prt:true ~prv:true ss id]
         in
         List.concat_map (fun (sym: Term.sym) ->
           match Timed.(!(sym.sym_not)) with
           | Term.Infix(assoc, prio) -> [Pratter.Infix assoc, prio, t]
           | Term.Prefix(prio) | Succ(Prefix(prio)) ->
               [Pratter.Prefix, prio, t]
           | Term.Postfix(prio) | Succ(Postfix(prio)) ->
               [Pratter.Postfix, prio, t]
           | _ -> []) sym
     | _ -> []

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
    let ops = ops find_sym st env in
    let p = Pratter.expression ~ops ~appl ~token:Fun.id in
    match Pratter.run p (List.to_seq (h :: args)) with
    | Ok e -> e
    | Error `Too_few_arguments ->
        Error.fatal t.pos "Malformed application in \"%a\"" Pretty.term t
    | Error `Op_conflict (t) ->
        Error.fatal t.pos "Operator conflict on \"%a\""
          Pretty.term t
end
include Pratt
