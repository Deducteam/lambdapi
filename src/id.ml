(** Metavariable identifiers. *)

open Extra

(** Representation of metavariable identifiers. *)
type t =
  | User of string
  | Sys  of int

(** [to_string id] returns a parsable identifier for [id]. *)
let to_string : t -> string = fun id ->
  match id with
  | User(s) -> Printf.sprintf "?%s" s
  | Sys(k)  -> Printf.sprintf "?%d" k

(** ['a map] is a datatype for finite maps from [id] to ['a]. *)
type 'a map =
  { str_map   : 'a StrMap.t
	; int_map   : 'a IntMap.t
	; free_keys : Cofin.t }

(** Empty map. *)
let empty : 'a map =
  { str_map   = StrMap.empty
	; int_map   = IntMap.empty
	; free_keys = Cofin.full }

(** [find id m] returns the data associated to [id] in the map
    [m]. It raises Not_found otherwise. *)
let find : t -> 'a map -> 'a = fun id m ->
  match id with
  | User(s) -> StrMap.find s m.str_map
  | Sys(k)  -> IntMap.find k m.int_map

(** [add_user s a m] maps [id] to [a] if [id=User s] or [find id m = a]. *)
let add_user : string -> 'a -> 'a map -> 'a map = fun s a m ->
  {m with str_map = StrMap.add s a m.str_map}

(** [add_sys k a m] maps [id] to [a] if [id=Sys k] or [find id m=a]. *)
let add_sys : (int -> 'a) -> 'a map -> 'a * 'a map = fun fn m ->
  let (k, free_keys) = Cofin.take_smallest m.free_keys in
  let v = fn k in
  (v, {m with int_map = IntMap.add k v m.int_map; free_keys})

(** [mem_sys k m] returns [true] iff [k] is mapped in [m]. *)
let mem_sys : int -> 'a map -> bool = fun k m ->
  Cofin.mem k m.free_keys
