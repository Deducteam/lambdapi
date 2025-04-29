open Core

(* indexing *)
val empty : unit -> unit
val load_rewriting_rules: string list -> unit
val index_sign : Sign.t -> unit
val dump : string -> unit -> unit

(* search command used by cli *)
val search_cmd_txt: Sig_state.sig_state -> string -> dbpath:string -> string

(* search command used by websearch *)
val search_cmd_html:
 Sig_state.sig_state
  -> from:int -> how_many:int -> string -> dbpath:string -> string
