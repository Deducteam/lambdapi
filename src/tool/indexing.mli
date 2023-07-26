(* indexing *)
val empty : unit -> unit
val index_sign : Core.Sign.t -> unit
val dump : unit -> unit

(* answers *)
type answer
val pp_item_set : answer Lplib.Base.pp

(* queries *)
type query = Parsing.SearchQuerySyntax.query

val answer_query :
  mok:(int -> Core.Term.meta option) -> Core.Env.env -> query -> answer

(* search commands used by tactics *)
val locate_name : string -> answer
val search_pterm :
  generalize:bool -> mok:(int -> Core.Term.meta option) -> Core.Env.env ->
   Parsing.Syntax.p_term -> answer

(* search commands used by cli *)
val locate_cmd_txt : string -> string
val search_cmd_txt : ?generalize:bool -> string -> string
val search_query_cmd_txt: string -> string

(* search commands used by webserver *)
val locate_cmd_html : string -> string
val search_cmd_html : ?generalize:bool -> string -> string
val search_query_cmd_html: string -> string
