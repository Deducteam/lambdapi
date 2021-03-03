(** Module paths in the Lambdapi library. *)

open Lplib.Base

module Path =
  struct
    (** Representation of a module name (roughly, a file path). *)
    type t = string list

    (** [pp ppf p] prints path [p] on the formatter [ppf]. Remark: to be used
       in Common only as it does not escape identifiers that need to be
       escaped. *)
    let pp : t pp = Lplib.List.pp Format.pp_print_string "."

    (** [compare] is a standard comparaison function for paths. *)
    let compare : t cmp = Stdlib.compare

    (** [of_string s] converts a string [s] lexed as qid into a path. *)
    let of_string : string -> t = Escape.split '.'

  end

include Path

(** Functional maps with paths as keys. *)
module Map = Map.Make(Path)
