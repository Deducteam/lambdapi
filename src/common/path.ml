(** Module paths in the Lambdapi library. *)

open Lplib open Base

module Path =
  struct
    (** Representation of a module name (roughly, a file path). *)
    type t = string list [@@deriving yojson]

    (** [pp ppf p] prints path [p] on the formatter [ppf]. Remark: to be used
       in Common only as it does not escape identifiers that need to be
       escaped. *)
    let pp : t pp = Lplib.List.pp string "."

    (** [compare] is a standard comparison function on paths. *)
    let compare : t cmp = Stdlib.compare

    let make (s : string) : t =
      if s = "" then []
      else
        s
        |> String.split_on_char '.'
        |> List.filter (fun x -> x <> "")
  end

include Path

module Set = Set.Make(Path)
module Map = Map.Make(Path)

(** [ghost s] creates a module path that cannot be entered by a user. *)
let ghost : string -> Path.t = fun s -> [""; s]

(** [default_dbpath] returns the default path of the index. *)
let default_dbpath : string =
  match Sys.getenv_opt "HOME" with
    | Some s -> Filename.concat s ".LPSearch.db"
    | None -> ".LPSearch.db"
