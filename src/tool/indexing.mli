open Core open Sig_state
open Parsing open Syntax

(* indexing *)
val empty : unit -> unit
val load_rewriting_rules: string list -> unit
val force_meta_rules_loading: unit -> unit
val index_sign : Sign.t -> unit
val parse_source_map : string -> unit (* the name of the file *)
val deindex_path : string -> unit
val dump : dbpath:string -> unit -> unit

val preserving_index : ('a -> 'b) -> 'a -> 'b

(* set by lsp; used to print the query results *)
val lsp_input : ((*uri*)string * (*text*)string) ref

(* search command used by cli *)
val search_cmd_txt_query: sig_state -> dbpath:string -> search -> string

(* search command used by websearch *)
val search_cmd_html:
sig_state -> from:int -> how_many:int -> string -> dbpath:string -> string

val search_cmd_txt: sig_state -> dbpath:string -> string Lplib.Base.pp
