(* indexing *)
val empty : unit -> unit
val load_rewriting_rules: string list -> unit
val index_sign : Core.Sign.t -> unit
val dump : string -> unit -> unit

(* search command used by cli *)
val search_cmd_txt: Core.Sig_state.sig_state -> string -> string -> string

(* search command used by websearch *)
val search_cmd_html:
 Core.Sig_state.sig_state
    -> from:int -> how_many:int -> string -> string -> string
