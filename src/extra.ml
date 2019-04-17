(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

module Int =
  struct
    type t = int
    let compare = (-)
  end

module String =
  struct
    include String

    let to_list : string -> char list = fun s ->
      let l = ref [] in
      String.iter (fun c -> l := c :: !l) s;
      List.rev !l

    let of_list : char list -> string = fun l ->
      let b = Buffer.create 37 in
      List.iter (Buffer.add_char b) l;
      Buffer.contents b
  end

module Option =
  struct
    type 'a t = 'a option

    let map : ('a -> 'b) -> 'a t -> 'b t = fun f o ->
      match o with
      | None    -> None
      | Some(e) -> Some(f e)

    let iter : ('a -> unit) -> 'a t -> unit = fun f o ->
      match o with
      | None    -> ()
      | Some(e) -> f e

    let get : 'a option -> 'a -> 'a = fun o d ->
      match o with
      | None    -> d
      | Some(e) -> e

    let equal : 'a eq -> 'a option eq = fun eq o1 o2 ->
      match (o1, o2) with
      | (None    , None    ) -> true
      | (Some(e1), Some(e2)) -> eq e1 e2
      | (_       , _       ) -> false
  end

module List =
  struct
    include List

    (** [pp pp_e sep oc l] prints the list [l] on the channel [oc] using [sep]
        as separator, and [pp_e] for printing the elements. *)
    let pp : 'a pp -> string -> 'a list pp = fun pp_elt sep oc l ->
      match l with
      | []    -> ()
      | e::es -> let fn e = Format.fprintf oc "%s%a" sep pp_elt e in
                 pp_elt oc e; iter fn es

    (** [map_find f l] applies [f] to the elements of list [l] (in order), and
        returns the result of the first application of [f] which result is not
        [None]. If none is found, [None] is returned. *)
    let rec map_find : ('a -> 'b option) -> 'a list -> 'b option = fun f l ->
      match l with
      | []    -> None
      | e::es -> match f e with None -> map_find f es | res -> res

    (** [cut l k] returns a pair of lists [(l1, l2)] such that [l1] has length
        [max (List.length l) k] and [l1 @ l2] is equal to [l]. *)
    let cut : 'a list -> int -> 'a list * 'a list = fun l k ->
      let rec cut acc l k =
        if k <= 0 then (List.rev acc, l) else
        match l with
        | []   -> (List.rev acc, l)
        | x::l -> cut (x::acc) l (k-1)
      in
      if k <= 0 then ([], l) else cut [] l k

    (** [add_array a1 a2 l] returns a list containing the elements of [l], and
        the (corresponding) elements of [a1] and [a2]. Note that [a1] and [a2]
        should have the same lenght otherwise [Invalid_argument] is raised. *)
    let add_array2 : 'a array -> 'b array -> ('a * 'b) list
        -> ('a * 'b) list = fun a1 a2 l ->
      let res = ref l in
      Array.iter2 (fun x1 x2 -> res := (x1,x2)::!res) a1 a2; !res

    (** [same_length l1 l2] returns [true] whenever [l1] and [l2] are lists of
        the same length. The function stops as soon as possible. *)
    let rec same_length : 'a list -> 'b list -> bool = fun l1 l2 ->
      match (l1, l2) with
      | ([]   , []   ) -> true
      | (_::l1, _::l2) -> same_length l1 l2
      | (_    , _    ) -> false

    (** [equal eq l1 l2] tests the equality of [l1] and [l2],  comparing their
        elements with [eq]. *)
    let equal : 'a eq -> 'a list eq = fun eq l1 l2 ->
      try List.for_all2 eq l1 l2 with Invalid_argument _ -> false
  end

module Array =
  struct
    include Array

    (** [for_all2 p a1 a2] checks if the corresponding elements of arrays [a1]
        and [a2] satisfy the predicate [p].  The [Invalid_argument]  exception
        is raised if the arrays do not have the same size. *)
    let for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool =
      fun f a1 a2 ->
        let exception Done in
        let f x y = if not (f x y) then raise Done in
        try iter2 f a1 a2; true with Done -> false

    (** [pp pp_e sep oc a] prints the array list [a] on the channel [oc] using
        [sep] as separator, and [pp_e] for printing the elements. *)
    let pp : 'a pp -> string -> 'a array pp = fun pp_elt sep oc a ->
      List.pp pp_elt sep oc (to_list a)

    (** [equal eq a1 a2] tests the equality of [a1] and [a2],  comparing their
        elements with [eq]. *)
    let equal : 'a eq -> 'a array eq = fun eq a1 a2 ->
      Array.length a1 = Array.length a2 && for_all2 eq a1 a2
  end

module Ord =
  struct
    (** Type of a total ordering function. A total ordering function [f] is a
        function such that [f x y] is zero if the two elements [x] and [y]
        are equal, [f x y] is strictly negative if [x] is smaller than [y],
        and [f x y] is strictly positive if [x] is greater than [y]. *)
    type 'a cmp = 'a -> 'a -> int

    (** [ord_lex ord] computes the lexicographic order corresponding to the
        alphabetical order [ord]. *)
    let rec ord_lex : 'a cmp -> 'a list cmp = fun ord l1 l2 ->
      match (l1, l2) with
      | [], []             -> 0
      | [], _              -> -1
      | _, []              -> 1
      | h1 :: t1, h2 :: t2 ->
          match ord h1 h2 with
          | 0 -> ord_lex ord t1 t2
          | x -> x
  end

(* Functional maps with [int] keys. *)
module IntMap = Map.Make(Int)

(* Functional maps with [string] keys. *)
module StrMap = Map.Make(String)

(** [time f x] times the application of [f] to [x], and returns the evaluation
    time in seconds together with the result of the application. *)
let time : ('a -> 'b) -> 'a -> float * 'b = fun f x ->
  let t = Sys.time () in
  let r = f x in (Sys.time () -. t, r)

(** Exception raised by the [with_timeout] function on a timeout. *)
exception Timeout

(** [with_timeout nbs f x] computes [f x] with a timeout of [nbs] seconds. The
    exception [Timeout] is raised if the computation takes too long, otherwise
    everything goes the usual way. *)
let with_timeout : int -> ('a -> 'b) -> 'a -> 'b = fun nbs f x ->
  let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout) in
  let old_behavior = Sys.signal Sys.sigalrm sigalrm_handler in
  let reset_sigalrm () =
    let _ = Unix.alarm 0 in
    Sys.set_signal Sys.sigalrm old_behavior
  in
  try
    let _ = Unix.alarm nbs in
    let res = f x in
    reset_sigalrm (); res
  with e -> reset_sigalrm (); raise e

(** [input_lines ic] reads the input channel [ic] line by line and returns its
    contents. The trailing newlines are removed in lines. The input channel is
    not closed by the function. *)
let input_lines : in_channel -> string list = fun ic ->
  let lines = ref [] in
  try
    while true do
      lines := input_line ic :: !lines
    done;
    assert false (* Unreachable. *)
  with End_of_file -> List.rev !lines
