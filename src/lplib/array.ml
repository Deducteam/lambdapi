module A = Stdlib.Array
include A
open Base

(** [for_all2 p a1 a2] checks if the corresponding elements of arrays [a1] and
    [a2] satisfy the predicate [p]. The [Invalid_argument] exception is raised
    if the arrays do not have the same size. *)
let for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool =
 fun f a1 a2 ->
  let exception Done in
  let f x y = if not (f x y) then raise Done in
  try iter2 f a1 a2; true with Done -> false

(** [pp pp_elt sep oc a] prints the array list [a] on the channel [oc] using
    [sep] as separator, and [pp_e] for printing the elements. *)
let pp : 'a pp -> string -> 'a array pp =
 fun pp_elt sep oc a ->
  let n = A.length a in
  if n > 0 then pp_elt oc (A.get a 0);
  for i = 1 to n - 1 do
    Format.fprintf oc "%s%a" sep pp_elt (A.get a i)
  done

(** [equal eq a1 a2] tests the equality of [a1] and [a2], comparing their
    elements with [eq]. *)
let equal : 'a eq -> 'a array eq =
 fun eq a1 a2 -> A.length a1 = A.length a2 && for_all2 eq a1 a2

(** [max_index ?cmp a] returns the index of the first maximum of array [a]
    according to comparison [?cmp]. If [cmp] is not given, defaults to
    [Stdlib.compare]. *)
let max_index : ?cmp:('a -> 'a -> int) -> 'a array -> int =
 fun ?(cmp = Stdlib.compare) arr ->
  let len = A.length arr in
  if len = 0 then invalid_arg "Extra.Array.max_index"
  else
    let max = ref 0 in
    for i = 1 to len - 1 do
      if cmp (A.get arr !max) (A.get arr i) < 0 then max := i
    done;
    !max

(** [max ?cmp a] returns the higher element according to comparison function
    [?cmp], using [Stdlib.compare] if not given, in array [a]. *)
let max : ?cmp:('a -> 'a -> int) -> 'a array -> 'a =
 fun ?(cmp = Stdlib.compare) arr -> A.get arr (max_index ~cmp arr)

(** [unzip a] is [List.unzip (Array.to_list a)]. *)
let unzip : ('a * 'b) array -> 'a list * 'b list = fun a ->
  let aux (el, er) (accl, accr) = (el :: accl, er :: accr) in
  A.fold_right aux a ([], [])

(** [drop n a] discards the first [n] elements of [a]. The empty array is
    returned if [n > length a]. *)
let drop : int -> 'a array -> 'a array = fun n a ->
  let l = length a in if n >= l then [||] else A.sub a n (l - n)
