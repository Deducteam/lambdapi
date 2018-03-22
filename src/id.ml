(** Metavariable identifiers. *)

open Extra

(** Representation of metavariable identifiers. *)
type t = string * int
(* NOTE: In a pair [(s,k)], [s] is called the prefix and [k] the suffix.
A pair [(s,k)] is valid iff:
- [s=""] and [k>=0] in which case [(s,k)] represents the meta [?k]
- [s<>""] and [k>=-1] in which case [(s,k)] represents the meta [?s] if [k<0]
   and [?sk] otherwise *)

(** [name id] returns a parsable identifier for [id]. *)
let name : t -> string = fun (s,k) ->
  if s<>"" && k<0 then Printf.sprintf "?%s" s else Printf.sprintf "?%s%d" s k

(** [pp oc id] pretty-prints [id] on the output channel [oc]. *)
let pp : out_channel -> t -> unit = fun oc id -> output_string oc (name id)

(** ['a map] is a datatype for finite maps from [id] to ['a]. *)
type 'a map = (int * 'a IntMap.t) StrMap.t

(** Empty map. *)
let empty : 'a map = StrMap.empty

(** [find id m] returns the data associated to [id] in the map
    [m]. It raises Not_found otherwise. *)
let find : t -> 'a map -> 'a = fun (s,k) m ->
  let _, ms = StrMap.find s m in
  IntMap.find k ms

(** [add id a m] maps [id'] to [a] if [id'=id] or [find id' m = a]. *)
let add : t -> 'a -> 'a map -> 'a map = fun (s,k) a m ->
  try
    let n, ms = StrMap.find s m in
    StrMap.add s (max n k, IntMap.add k a ms) m
  with Not_found ->
    StrMap.add s (k, IntMap.add k a IntMap.empty) m

(** [fresh s m] returns an id with prefix [s] not mapped in [m]. *)
let fresh : string -> 'a map -> t = fun s m ->
  try let n, _ = StrMap.find s m in s, n+1
  with Not_found -> s, -1

(** [add_fresh s a m] is equivalent to [let id = fresh s m in id, add id a
    m] but a little bit more efficient. *)
let add_fresh : string -> 'a -> 'a map -> t * 'a map = fun s a m ->
  try
    let n, ms = StrMap.find s m in
    let k = n+1 in
    (s,k), StrMap.add s (k, IntMap.add k a ms) m
  with Not_found ->
    (s,-1), StrMap.add s (-1, IntMap.add (-1) a IntMap.empty) m
