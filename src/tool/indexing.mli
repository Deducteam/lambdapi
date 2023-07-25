type item
module ItemSet : Set.S with type elt = item
val pp_item_set : ItemSet.t Lplib.Base.pp
val html_of_item_set : ItemSet.t Lplib.Base.pp

val empty : unit -> unit
val index_sign : Core.Sign.t -> unit
val dump : unit -> unit

(* search commands used by tactics *)
val locate_name : string -> ItemSet.t
val search_pterm :
  holes_in_index:bool -> mok:(int -> Core.Term.meta option) -> Core.Env.env ->
   Parsing.Syntax.p_term -> ItemSet.t

(* search commands used by cli *)
val locate_cmd_txt : string -> string
val locate_cmd_html : string -> string

(* search commands used by webserver *)
val search_cmd_html : ?holes_in_index:bool -> string -> string
val search_cmd_txt : ?holes_in_index:bool -> string -> string
