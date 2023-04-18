open Core.Term

type sym_name = Common.Path.t * string
val name_of_sym : sym -> sym_name

type 'a db

val empty : 'a db
val insert : ('a -> string) -> 'a db -> term -> 'a -> 'a db
val search : 'a db -> term -> 'a list
val resolve_name : 'a db -> string -> 'a list

module DB : sig
 type item = sym_name * Common.Pos.pos option
 val insert : term -> item -> unit
 val search : term -> item list
 val resolve_name : string -> item list

 val dump_to : filename:string -> unit
 val restore_from : filename:string -> unit
end 
