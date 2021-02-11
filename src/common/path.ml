(** Module paths in the Lambdapi library. *)

open Lplib.Base

module Path = struct
  (** Representation of a module name (roughly, a file path). *)
  type t = string list

  (** [compare] is a standard comparing function for module names. *)
  let compare : t -> t -> int = fun m1 m2 ->
    Stdlib.compare (List.map Escape.unescape m1)
                   (List.map Escape.unescape m2)

  (** [pp ppf mp] prints [mp] on formatter [ppf]. *)
  let pp : t pp = fun ppf mp ->
    Format.pp_print_string ppf (String.concat "." mp)

  (** [ghost s] creates a special module of name [s] that cannot be handled
      by users. *)
  let ghost : string -> t = fun s -> [""; s]

  (** [of_string s] converts a string [s] lexed as qid into a path. *)
  let of_string : string -> t = Escape.split '.'
end

include Path

(** Functional maps with module names as keys. *)
module Map = Map.Make(Path)
