(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = out_channel -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

module Int =
  struct
    type t = int
    let compare = (-)
  end

module List =
  struct
    include List

    (** [pp pp_e sep oc l] prints the list [l] on the channel [oc] using [sep]
        as separator, and [pp_e] for printing the elements. *)
    let pp : 'a pp -> string -> 'a list pp = fun pp_elt sep oc l ->
      match l with
      | []    -> ()
      | e::es -> let fn e = Printf.fprintf oc "%s%a" sep pp_elt e in
                 pp_elt oc e; iter fn es

    (** [map_find f l] applies [f] to the elements of list [l] (in order), and
        returns the result of the first application of [f] which result is not
        [None]. If none is found, [None] is returned. *)
    let rec map_find : ('a -> 'b option) -> 'a list -> 'b option = fun f l ->
      match l with
      | []    -> None
      | e::es -> match f e with None -> map_find f es | res -> res

    (** [cut l k] returns a pair of lists [(l1,l2)] such that [l1] has length
        [max (List.length l) k] and [l1 @ l2] is equal to [l]. *)
    let cut : 'a list -> int -> 'a list * 'a list = fun l k ->
      let rec cut acc l k =
        if k <= 0 then (List.rev acc, l) else
        match l with
        | []   -> (List.rev acc, l)
        | x::l -> cut (x::acc) l (k-1)
      in
      if k <= 0 then ([], l) else cut [] l k
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
  end

module Stack =
  struct
    include Stack

    (** [mem e s] checks whether the element [e] occurs in the stack [s]. *)
    let mem : 'a -> 'a t -> bool = fun e s ->
      let test x = if x = e then raise Exit in
      try iter test s; false with Exit -> true
  end

(** [time f x] times the application of [f] to [x], and returns the evaluation
    time in seconds together with the result of the application. *)
let time : ('a -> 'b) -> 'a -> float * 'b = fun f x ->
  let t = Sys.time () in
  let r = f x in (Sys.time () -. t, r)

(* Functional maps with [int] keys. *)
module IntMap = Map.Make(Int)

(* Functional maps with [string] keys. *)
module StrMap = Map.Make(String)

(** Representation of a “cofinite” set of positive numbers (close enough). *)
module Cofin =
  struct
    (** Representation of a cofinite set of positive numbers, represented with
        a sorted list of disjoint ranges which contents is not in the set. *)
    type t = (int * int) list

    (** [full] set of all the positive numbers, which are the elements of tyme
        [int] from [0] to [Pervasives.max_int]. *)
    let full : t = []

    (** [mem i s] returns [true] if [i] is contained in the set [s]. Note that
        [i] should be greater or equal to [0], otherwise [Invalid_argument] is
        raised. *)
    let mem : int -> t -> bool = fun i s ->
      if i < 0 then invalid_arg "Cofinite.mem";
      List.for_all (fun (l,r) -> i < l || i > r) s

    (* Internal function. *)
    let rec normalize : t -> t = fun s ->
      match s with
      (* Checking for broken invariants. *)
      | (l1,r1) :: _            when l1 > r1   -> assert false
      | (_ ,r1) :: (l2,_ ) :: _ when r1 > l2   -> assert false
      (* Normal cases. *)
      | (l1,r1) :: (l2,r2) :: s when r1+1 = l2 -> normalize ((l1,r2) :: s)
      | (l1,r1) :: s                           -> (l1,r1) :: normalize s
      | []                                     -> []

    (** [remove i s] returns a set containing the same elements as [s], except
        [i] which is not contained in the returned set. If [i] does not appear
        in [s] then the exception [Invalid_argument] is raised. *)
    let remove : int -> t -> t = fun i s ->
      let rec remove i s =
        match s with
        | []                  -> [(i,i)]
        | (l,_)::_ when i < l -> (i,i) :: s
        | (l,r)::s when i > r -> (l,r) :: remove i s
        | _                   -> invalid_arg "Cofinite.remove";
      in
      normalize (remove i s)

    (** [smallest s] returns the value of the smallest element of [s]. *)
    let smallest : t -> int = fun s ->
      match s with
      | [(0,n)] when n = max_int -> assert false
      | (0,n)::_                 -> n+1
      | _                        -> 0

    (** [take_smallest s] returns a couple [(i,t)] in which [i] is the element
        of [s] that is the smallest, and [t] is a copy of [s] in which [i] has
        been removed. *)
    let take_smallest : t -> int * t = fun s ->
      let i = smallest s in
      (i, remove i s)

    (** [pp oc s] outputs a representation of the set [s] on channel [oc]. *)
    let pp : out_channel -> t -> unit = fun oc s ->
      let pelt oc (l,r) =
        if l = r then Printf.fprintf oc "{%i}" l
        else Printf.fprintf oc "[%i..%i]" l r
      in
      match s with
      | []   -> Printf.fprintf oc "<int>"
      | [c]  -> Printf.fprintf oc "<int> - %a" pelt c
      | c::s -> Printf.fprintf oc "<int> - (%a" pelt c;
                List.iter (Printf.fprintf oc "∪%a" pelt) s;
                Printf.fprintf oc ")"
  end
