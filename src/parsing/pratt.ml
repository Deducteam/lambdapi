(** Parsing of infix operators using the Pratter library.

    The interface for the Pratter library can be seen at
    @see <https://forge.tedomum.net/koizel/pratter>. *)

open Lplib open Extra
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
 
  (* Convert a signature state and an environment to a pratter operators
     structure. *)
  let ops_of_sig_state : Sig_state.find_sym -> Sig_state.t -> Env.t
                         -> (p_term, p_term) Pratter.Operators.t =
   fun find_sym st env ->
     let f (looking_for: Term.sym) (t: p_term): p_term option =
       match t.elt with
       | P_Iden({elt=(mp, s); _} as id, false) ->
           let open Option.Monad in
           let* sym =
             try (* Look if [id] is in [env]... *)
               if mp <> [] then raise Not_found;
               ignore (Env.find s env); None
             with Not_found -> (* ... or look into the signature *)
               Some(find_sym ~prt:true ~prv:true st id)
           in
           if (sym.sym_name = looking_for.sym_name &&
               sym.sym_path = looking_for.sym_path)
           then Some t
           else None
       | _ -> None
     in
     StrMap.fold (fun _ s ops ->
       match Timed.(!(s.Term.sym_not)) with
       | Term.Infix(assoc, prio) ->
           Pratter.Operators.(infix (f s) assoc prio <+> ops)
       | Term.Prefix(prio) | Succ(Prefix(prio)) ->
           Pratter.Operators.(prefix (f s) prio <+> ops)
       | Term.Postfix(prio) | Succ(Postfix(prio)) ->
           Pratter.Operators.(postfix (f s) prio <+> ops)
       | _ -> ops) Timed.(!(st.signature.sign_symbols)) Pratter.Operators.none
       
   let appl : p_term -> p_term -> p_term = fun t u ->
     Pos.make (Pos.cat t.pos u.pos) (P_Appl(t, u))
  
  (* NOTE the term is converted from appl nodes to list in [Pratt.parse],
   rebuilt into appl nodes by [Pratt.parse], and then decomposed again into a
   list by [get_args]. We could make [Pratt.parse] return a list of terms
   instead. *)
  let parse : ?find_sym:Sig_state.find_sym -> Sig_state.t -> Env.t -> p_term -> p_term =
    fun ?(find_sym=Sig_state.find_sym) st env t ->
    let h, args = Syntax.p_get_args t in
    (* Note that [ops] is built each time a term is parsed. We could
       spare some computations by memoizing [ops_of_sig_state] or pre-computing it. *)
    let ops = ops_of_sig_state find_sym st env in
    let parser = Pratter.expression ~appl ~token:Fun.id ~ops in
    match Pratter.run parser (List.to_seq (h :: args)) with
    | Ok e -> e
    | Error (`Op_conflict t) ->
        Error.fatal t.pos "Operator conflict on \"%a\"." Pretty.term t
    | Error `Too_few_arguments ->
        Error.fatal t.pos "Malformed application in \"%a\"" Pretty.term t
end
include Pratt
