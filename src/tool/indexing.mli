(* indexing *)
val empty : unit -> unit
val index_sign : Core.Sign.t -> unit
val dump : unit -> unit

(* answers *)
type answer
val pp_item_set : answer Lplib.Base.pp

(* query language *)
type side = Lhs | Rhs
type inside = Exact | Inside
type 'inside where =
 | Spine of 'inside
 | Conclusion of 'inside
 | Hypothesis of 'inside
type constr =
 | QType of (inside option) where option
 | QXhs  of inside option * side option
type base_query =
 | QName of string
 | QSearch of Parsing.Syntax.p_term * (*holes_in_index:*)bool * constr option
type op =
 | Intersect
 | Union
type filter =
 | Path of string
type query =
 | QBase of base_query
 | QOpp of query * op * query
 | QFilter of query * filter

val answer_query :
  mok:(int -> Core.Term.meta option) -> Core.Env.env -> query -> answer

(* search commands used by tactics *)
val locate_name : string -> answer
val search_pterm :
  holes_in_index:bool -> mok:(int -> Core.Term.meta option) -> Core.Env.env ->
   Parsing.Syntax.p_term -> answer

(* search commands used by cli *)
val locate_cmd_txt : string -> string
val locate_cmd_html : string -> string

(* search commands used by webserver *)
val search_cmd_html : ?holes_in_index:bool -> string -> string
val search_cmd_txt : ?holes_in_index:bool -> string -> string
