type item
module ItemSet : Set.S with type elt = item
val pp_item_set : ItemSet.t Lplib.Base.pp

val empty : unit -> unit
val index_sign : Core.Sign.t -> unit
val dump : unit -> unit

val locate_name : string -> ItemSet.t
val search : Core.Term.term -> ItemSet.t
val search_pterm : Parsing.Syntax.p_term -> ItemSet.t
