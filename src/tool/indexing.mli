(* indexing *)
val empty : unit -> unit
val index_sign : rules:string list -> Core.Sign.t -> unit
val dump : unit -> unit

val query_results: Parsing.Syntax.query -> string

(* search command used by cli *)
val search_cmd_txt: string -> string

(* search command used by websearch *)
val search_cmd_html: string -> string
