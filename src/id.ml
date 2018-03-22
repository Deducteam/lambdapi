(** Metavariable identifiers. *)

open Extra

(** Representation of metavariable identifiers. *)
type t = User of string | Sys of int

(** [name id] returns a parsable identifier for [id]. *)
let name : t -> string = fun id ->
  match id with
  | User s -> Printf.sprintf "?%s" s
  | Sys k -> Printf.sprintf "?%d" k

(** [pp oc id] pretty-prints [id] on the output channel [oc]. *)
let pp : out_channel -> t -> unit = fun oc id -> output_string oc (name id)

(** ['a map] is a datatype for finite maps from [id] to ['a]. *)
type 'a map = { m_user : 'a StrMap.t
	      ; m_sys : 'a IntMap.t
	      ; m_max : int }

(** Empty map. *)
let empty : 'a map = { m_user = StrMap.empty
		     ; m_sys = IntMap.empty
		     ; m_max = -1 }

(** [find id m] returns the data associated to [id] in the map
    [m]. It raises Not_found otherwise. *)
let find : t -> 'a map -> 'a = fun id m ->
  match id with
  | User s -> StrMap.find s m.m_user
  | Sys k -> IntMap.find k m.m_sys

(** [add_user s a m] maps [id] to [a] if [id=User s] or [find id m = a]. *)
let add_user : string -> 'a -> 'a map -> 'a map = fun s a m ->
  { m with m_user = StrMap.add s a m.m_user }

(** [add_sys k a m] maps [id] to [a] if [id=Sys k] or [find id m=a]. *)
let add_sys : int -> 'a -> 'a map -> 'a map = fun k a m ->
  { m_user = m.m_user
  ; m_sys = IntMap.add k a m.m_sys
  ; m_max = max m.m_max k }

(** [fresh m] generates a system identifier not mapped in [m]. *)
let fresh : 'a map -> int = fun m -> m.m_max

(** [mem_sys k m] returns [true] iff [k] is mapped in [m]. *)
let mem_sys : int -> 'a map -> bool = fun k m -> k <= m.m_max
(*if k > m.m_max then false else IntMap.mem k m.m_sys*)
