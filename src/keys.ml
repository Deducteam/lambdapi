open Extra

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
        | (l,r)::_ when i < l -> (i,i) :: s
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

(** Representation of a map with [int] keys (greater or equal to [0]) and with
    values of the given type ['a]. *)
type 'a map =
  { mapping   : 'a IntMap.t
  ; free_keys : Cofin.t }

(** [empty] is the empty map, with no mapping. *)
let empty : 'a map =
  { mapping   = IntMap.empty
  ; free_keys = Cofin.full }

(** [find k m] returns the value mapped to the non-negative integer key [k] in
    the map [m]. The exception [Not_found] is raised if it is not mapped. When
    [k] is invalid (negative), [Invalid_argument] is raised. *)
let find : int -> 'a map -> 'a = fun k m ->
  if k < 0 then invalid_arg "Keys.find";
  IntMap.find k m.mapping

(** [add fn m] finds the smallest available key [k] in [m], and then maps this
    key to the value [fn k] in a copy of the map [m]. The function returns the
    couple of the effectively inserted value and the extended map. *)
let add : (int -> 'a) -> 'a map -> 'a * 'a map = fun fn m ->
  let (k, free_keys) = Cofin.take_smallest m.free_keys in
  let v = fn k in
  let mapping = IntMap.add k v m.mapping in
  (v, {mapping; free_keys})

(** [add_with_key k v m] inserts the binding [(k,v)] in the map [v],  provided
    that the key [k] is a valid (non-negative) and available. When this is not
    the case, the [Invalid_argument] exception is raised. *)
let add_with_key : int -> 'a -> 'a map -> 'a map = fun k v m ->
  if k < 0 then invalid_arg "Keys.add_with_key";
  if not (Cofin.mem k m.free_keys) then invalid_arg "Keys.add_with_key";
  let mapping   = IntMap.add k v m.mapping in
  let free_keys = Cofin.remove k m.free_keys in
  {mapping; free_keys}
