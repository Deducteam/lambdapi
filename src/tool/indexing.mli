type sym_name = Common.Path.t * string
val name_of_sym : Core.Term.sym -> sym_name

(*
type 'a db

val empty : 'a db
val insert : ('a -> string) -> 'a db -> Core.Term.term -> 'a -> 'a db
val search : 'a db -> Core.Term.term -> 'a list
val resolve_name : 'a db -> string -> 'a list
*)

module DB : sig
 type item = sym_name * Common.Pos.pos option
 val insert : Core.Term.term -> item -> unit
 val resolve_name : string -> item list
 val search : Core.Term.term -> item list
 val search_pterm : Parsing.Syntax.p_term -> item list

 val find_sym : Core.Sig_state.find_sym

 val dump_to : filename:string -> unit
 val restore_from : filename:string -> unit

 val pp_item_list : item list Lplib.Base.pp
end 