open Core

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
val search_cmd_txt:
 Sig_state.sig_state -> dbpath:string -> string Lplib.Base.pp

(* search command used by websearch *)
val search_cmd_html:
 Sig_state.sig_state
  -> from:int -> how_many:int -> string -> dbpath:string -> string
