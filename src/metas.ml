(** Metavariables *)

open Terms
open Extra

type map = meta StrMap.t

(** [unset u] returns [true] if [u] is not instanciated. *)
let unset : meta -> bool = fun u -> !(u.meta_value) = None

let internal (m:meta) : bool =
  match m.meta_name with
  | User(_)  -> false
  | Sys(_) -> true

(** Representation of the existing meta-variables. *)
type meta_map =
  { str_map   : meta StrMap.t
  ; int_map   : meta IntMap.t
  ; free_keys : Cofin.t }

(** [empty_meta_map] is an emptu meta-variable map. *)
let empty_meta_map : meta_map =
  { str_map   = StrMap.empty
  ; int_map   = IntMap.empty
  ; free_keys = Cofin.full }

(** [all_metas] is the reference in which the meta-variables are stored. *)
let all_metas : meta_map ref = ref empty_meta_map

(** [meta_stats ()] returns a couple [(nbi,nbs)] where [nbi] (resp. [nbs])  is
    the number of internal (resp. user-defined) metavariables that are defined
    in the system at the time of the call. *)
let meta_stats : unit -> int * int = fun () ->
  (IntMap.cardinal !all_metas.int_map, StrMap.cardinal !all_metas.str_map)

(** [print_meta_stats fmt] prints statistics about the metavariables that  are
    currently defined on the [fmt] channel. *)
let print_meta_stats : Format.formatter -> unit -> unit = fun fmt () ->
  let (nbi, nbs) = meta_stats () in
  Format.fprintf fmt "%i system %i user" nbi nbs

(** [find_meta name] returns the meta-variable mapped to [name] in [all_metas]
    or raises [Not_found] if the name is not mapped. *)
let find_meta : meta_name -> meta = fun name ->
  match name with
  | User(s) -> StrMap.find s !all_metas.str_map
  | Sys(k) -> IntMap.find k  !all_metas.int_map

(** [exists_meta name] tells whether [name] is mapped in [all_metas]. *)
let exists_meta : meta_name -> bool = fun name ->
  match name with
  | User(s) -> StrMap.mem s !all_metas.str_map
  | Sys(k) -> IntMap.mem k  !all_metas.int_map

(** [add_user_meta s a n] creates a new user-defined meta-variable
    named [s], of type [a] and arity [n]. Note that [all_metas] is
    updated automatically at the same time. *)
let add_user_meta : string -> term -> int -> meta = fun s a n ->
  let m = { meta_name  = User(s)
          ; meta_type  = ref a
          ; meta_arity = n
          ; meta_value = ref None }
  in
  let str_map = StrMap.add s m !all_metas.str_map in
  all_metas := {!all_metas with str_map}; m

(** [add_sys_meta a n] creates a new internal meta-variable of type
    [a] and arity [n]. Note that [all_metas] is updated automatically
    at the same time. *)
let add_sys_meta : term -> int -> meta = fun a n ->
  let (k, free_keys) = Cofin.take_smallest !all_metas.free_keys in
  let m = { meta_name  = Sys(k)
          ; meta_type  = ref a
          ; meta_arity = n
          ; meta_value = ref None }
  in
  let int_map = IntMap.add k m !all_metas.int_map in
  all_metas := {!all_metas with int_map; free_keys}; m
