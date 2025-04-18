module A = Stdlib.Array
include A

open Base

(** [for_all2 p a1 a2] checks if the corresponding elements of arrays [a1] and
    [a2] satisfy the predicate [p]. The [Invalid_argument] exception is raised
    if the arrays do not have the same size. *)
let for_all2 : ('a -> 'b -> bool) -> 'a array -> 'b array -> bool =
 fun f a1 a2 ->
 (*let exception Done in
   let f x y = if not (f x y) then raise Done in
   try iter2 f a1 a2; true with Done -> false*)
 (*code taken from Stdlib:*)
 let n1 = length a1
 and n2 = length a2 in
 if n1 <> n2 then invalid_arg "Array.for_all2"
 else let rec loop i =
        if i = n1 then true
        else if f (unsafe_get a1 i) (unsafe_get a2 i) then loop (succ i)
        else false in
      loop 0

(** [pp elt sep ppf a] prints the array [a] on the formatter [ppf] using
    [sep] as separator and [elt] for printing the elements. *)
let pp : 'a pp -> string -> 'a array pp =
 fun elt sep oc a ->
  let n = A.length a in
  if n > 0 then elt oc (A.get a 0);
  for i = 1 to n - 1 do
    out oc "%s%a" sep elt (A.get a i)
  done

(** Comparison function on arrays. *)
let cmp : 'a cmp -> 'a array cmp = fun cmp_elt ->
  let cmp a1 a2 (* of the same length *) =
    let exception Distinct of int in
    let rec cmp i =
      if i >= 0 then
        match cmp_elt (A.get a1 i) (A.get a2 i) with
        | 0 -> cmp (i - 1)
        | n -> raise (Distinct n)
    in
    try cmp (A.length a1 - 1); 0 with Distinct n -> n
  in
  fun a1 a2 ->
  if a1 == a2 then 0
  else lex (cmp_map Stdlib.compare A.length) cmp (a1,a1) (a2,a2)

(** [eq eq_elt a1 a2] tests the equality of [a1] and [a2], comparing their
    elements with [eq_elt]. *)
let eq : 'a eq -> 'a array eq = fun eq_elt a1 a2 ->
  a1 == a2 || (A.length a1 = A.length a2 && for_all2 eq_elt a1 a2)

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
