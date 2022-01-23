(** Module paths in the Lambdapi library. *)

open Lplib open Base

module Path =
  struct
    (** Representation of a module name (roughly, a file path). *)
    type t = string list

    (** [pp ppf p] prints path [p] on the formatter [ppf]. Remark: to be used
       in Common only as it does not escape identifiers that need to be
       escaped. *)
    let pp : t pp = Lplib.List.pp Format.pp_print_string "."

    (** [compare] is a standard comparison function on paths. *)
    let compare : t cmp = Stdlib.compare

  end

include Path

module Set = Set.Make(Path)
module Map = Map.Make(Path)
