(** Module paths in the Lambdapi library. *)

open Lplib.Base

module Path =
  struct
    (** Representation of a module name (roughly, a file path). *)
    type t = string list

    (** [pp ppf p] prints path [p] on the formatter [ppf]. *)
    let pp : t pp = Lplib.List.pp Format.pp_print_string "."

    (** [compare] is a standard comparaison function for paths. *)
    let compare : t cmp = Stdlib.compare

    (** [ghost s] creates from [s] a special path that cannot be handled by
       users. We use the fact that the empty string is not a valid (even
       escaped) identifier. *)
    let ghost : string -> t = fun s -> [""; s]

    (** [of_string s] converts a string [s] lexed as qid into a path. *)
    let of_string : string -> t = Escape.split '.'

  end

include Path

(** Functional maps with paths as keys. *)
module Map = Map.Make(Path)
