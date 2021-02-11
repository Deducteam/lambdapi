(** Module paths in the Lambdapi library. *)

open Lplib.Base

module Path :
sig
  (** Representation of a module name (roughly, a file path). *)
  type t = string list

  (** [compare] is a standard comparing function for module names. *)
  val compare : t cmp
  val eq : t eq

  (** [pp ppf mp] prints [mp] on formatter [ppf]. *)
  val pp : t pp

  (** [ghost s] creates a special module of name [s] that cannot be handled
      by users. *)
  val ghost : string -> t

  (** [of_string s] converts a string [s] lexed as qid into a path. *)
  val of_string : string -> t
end
  =
  struct
    type t = string list

    (* To compare paths, we unescape them to identify "{|p|}" and "p" when p
       is a regular identifier. *)
    let compare p1 p2 =
      Stdlib.compare (List.map Escape.unescape p1)
                     (List.map Escape.unescape p2)

    let eq p1 p2 = compare p1 p2 = 0

    let pp ppf p = Format.pp_print_string ppf (String.concat "." p)

    let ghost s = [""; s]

    let of_string = Escape.split '.'
  end

include Path

(** Functional maps with paths as keys. *)
module Map = Map.Make(Path)

(** Stacks of paths (using Path.eq for testing membership). *)
module Stack :
sig
  type t
  val empty : t
  val add : Path.t -> t -> t
  val hd : t -> Path.t
  val tl : t -> t
  val mem : Path.t -> t -> bool
  val iter : (Path.t -> unit) -> t -> unit
end
  =
  struct
    type t = Path.t list
    let empty = []
    let add p ps = p::ps
    let hd = function p::_ -> p | [] -> invalid_arg __LOC__
    let tl = function _::ps -> ps | [] -> invalid_arg __LOC__
    let mem p = List.exists (Path.eq p)
    let iter = List.iter
  end
