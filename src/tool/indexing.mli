type item
val pp_item_list : item list Lplib.Base.pp

val empty : unit -> unit
val index_sign : Core.Sign.t -> unit
val dump : unit -> unit

val locate_name : string -> item list
val search : Core.Term.term -> item list
val search_pterm : Parsing.Syntax.p_term -> item list
