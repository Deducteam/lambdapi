open Core open Sig_state
open Parsing open Syntax

(* indexing *)
val empty : unit -> unit
val load_rewriting_rules: string list -> unit
val index_sign : Sign.t -> unit
val dump : dbpath:string -> unit -> unit

(* search command used by cli *)
val search_cmd_txt: sig_state -> dbpath:string -> string -> string
val search_cmd_txt_query: sig_state -> dbpath:string -> search -> string

(* search command used by websearch *)
val search_cmd_html:
 sig_state -> from:int -> how_many:int -> dbpath:string -> string -> string
