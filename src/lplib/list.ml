module L = Stdlib.List
include L

let zip = combine
let unzip = split

open Base

(** [pp elt sep ppf l] prints the list [l] on the formatter [ppf] using
   [sep] as separator, and [elt] for printing the elements. *)
let pp : 'a pp -> unit outfmt -> 'a list pp = fun elt sep ->
  Format.pp_print_list ~pp_sep:(unit sep) elt

(** Total order on lists. *)
let cmp : 'a cmp -> 'a list cmp = fun cmp_elt ->
  let rec cmp l l' =
    match l, l' with
    | [], [] -> 0
    | [], _::_ -> -1
    | _::_, [] -> 1
    | x::l, x'::l' -> lex cmp_elt cmp (x,l) (x',l')
  in cmp

(** [eq eq_elt l1 l2] tests the equality of [l1] and [l2], comparing their
    elements with [eq_elt]. *)
let eq : 'a eq -> 'a list eq = fun eq_elt l1 l2 ->
  try L.for_all2 eq_elt l1 l2 with Invalid_argument _ -> false

(** [find_map f l] applies [f] to the elements of [l] in order, and returns
   the first result of the form [Some v], or [None] if none exist.
   @since 4.10.0 *)
let rec find_map f = function
  | [] -> None
  | x :: l ->
     begin match f x with
       | Some _ as result -> result
       | None -> find_map f l
     end

(** [filter_map f l] applies [f] to every element of [l], filters
    out the [None] elements and returns the list of the arguments of
    the [Some] elements.
    @since 4.08.0 *)
let filter_map : ('a -> 'b option) -> 'a list -> 'b list = fun f ->
  let rec aux accu = function
    | [] -> rev accu
    | x :: l ->
        match f x with
        | None -> aux accu l
        | Some v -> aux (v :: accu) l
  in
  aux []

(** [concat_map f l] gives the same result as
    {!concat}[ (]{!map}[ f l)]. Tail-recursive.
    @since 4.10.0 *)
let concat_map f l =
  let rec aux f acc = function
    | [] -> rev acc
    | x :: l ->
       let xs = f x in
       aux f (rev_append xs acc) l
  in aux f [] l

(** [filter_rev_map f l] is equivalent to [filter_map f (List.rev l)], but it
    only traverses the list once and is tail-recursive. *)
let filter_rev_map : ('a -> 'b option) -> 'a list -> 'b list = fun f ->
  let rec aux acc = function
    | [] -> acc
    | hd :: tl ->
        match f hd with
        | Some x -> aux (x :: acc) tl
        | None -> aux acc tl
  in aux []

(** [filteri_map f l] applies [f] element wise on [l] and keeps [x] such that
    for [e] in [l], [f e = Some(x)]. *)
let filteri_map : (int -> 'a -> 'b option) -> 'a list -> 'b list = fun f l ->
  let rec loop k = function
    | [] -> []
    | h :: t -> (
      match f k h with
      | Some x -> x :: loop (succ k) t
      | None -> loop (succ k) t )
  in loop 0 l

(** [cut l k] returns a pair of lists [(l1, l2)] such that [l1] has length
    [min (List.length l) k] and [l1 @ l2] is equal to [l]. *)
let cut : 'a list -> int -> 'a list * 'a list = fun l k ->
  let rec cut acc l k =
    if k <= 0 then (L.rev acc, l)
    else match l with
         | [] -> (L.rev acc, l)
         | x :: l -> cut (x :: acc) l (k - 1)
  in
  if k <= 0 then ([], l) else cut [] l k

let _ =
  assert (cut [1;2;3] 0 = ([], [1;2;3]));
  assert (cut [1;2;3] 1 = ([1], [2;3]));
  assert (cut [1;2;3] 2 = ([1;2], [3]));
  assert (cut [1;2;3] 3 = ([1;2;3], []));
  assert (cut [1;2;3] 4 = ([1;2;3], []))

(** [add_array a1 a2 l] returns a list containing the elements of [l], and the
    (corresponding) elements of [a1] and [a2]. Note that [a1] and [a2] should
    have the same lenght otherwise [Invalid_argument] is raised. *)
let add_array2 : 'a array -> 'b array -> ('a * 'b) list -> ('a * 'b) list =
 fun a1 a2 l ->
  let res = ref l in
  Array.iter2 (fun x1 x2 -> res := (x1, x2) :: !res) a1 a2;
  !res

(** [same_length l1 l2] returns [true] whenever [l1] and [l2] are lists of the
    same length. The function stops as soon as possible. *)
let rec same_length : 'a list -> 'b list -> bool = fun l1 l2 ->
  match l1, l2 with
  | [], [] -> true
  | _ :: l1, _ :: l2 -> same_length l1 l2
  | _ -> false

(** [max ?cmp l] finds the max of list [l] with compare function [?cmp]
    defaulting to [Stdlib.compare].
    @raise Invalid_argument if [l] is empty. *)
let max : ?cmp:('a -> 'a -> int) -> 'a list -> 'a =
 fun ?(cmp = Stdlib.compare) li ->
  match li with
  | [] -> invalid_arg "Extra.List.max"
  | h :: t ->
    let max e1 e2 = if cmp e1 e2 >= 0 then e1 else e2 in
    L.fold_left max h t

(** [assoc_eq e k l] is [List.assoc k l] with equality function [e].
    @raise Not_found if [k] is not a key of [l]. *)
let assoc_eq : 'a eq -> 'a -> ('a * 'b) list -> 'b = fun eq k ->
  let rec loop = function
    | [] -> raise Not_found
    | (x, e) :: _ when eq x k -> e
    | _ :: t -> loop t
  in loop

(** [remove_phys_dups l] uniqify list [l] keeping only the last element, using
    physical equality. *)
let rec remove_phys_dups : 'a list -> 'a list = function
  | [] -> []
  | x :: xs ->
    let xs = remove_phys_dups xs in if L.memq x xs then xs else x :: xs

(** [destruct l i] returns a triple [(left_rev, e, right)] where [e] is the
    [i]-th element of [l], [left_rev] is the reversed prefix of [l] up to its
    [i]-th element (excluded), and [right] is the remaining suffix of [l]
    (starting at its [i+1]-th element).
    @raise Invalid_argument when [i < 0].
    @raise Not_found when [i ≥ length v]. *)
let destruct : 'a list -> int -> 'a list * 'a * 'a list =
  let rec destruct l i r =
    match r, i with
    | [], _ -> raise Not_found
    | v :: r, 0 -> (l, v, r)
    | v :: r, i -> destruct (v :: l) (i - 1) r
  in
  fun e i ->
  if i < 0 then invalid_arg __LOC__;
  destruct [] i e

(** [reconstruct left_rev l right] concatenates (reversed) [left_rev], [l] and
    [right]. This function will typically be used in combination with
    {!val:destruct} to insert a sublist [l] in the place of the element at
    the specified position in the specified list. *)
let reconstruct : 'a list -> 'a list -> 'a list -> 'a list = fun l m r ->
  L.rev_append l (m @ r)

(** [init n f] creates a list with [f 0] up to [f n] as its elements. Note
   that [Invalid_argument] is raised if [n] is negative. *)
let init : int -> (int -> 'a) -> 'a list = fun n f ->
  if n < 0 then invalid_arg "Extra.List.init";
  let rec loop k = if k > n then [] else f k :: loop (k + 1) in
  loop 0

(** [mem_sorted cmp x l] tells whether [x] is in [l] assuming that [l] is
   sorted wrt [cmp]. *)
let mem_sorted : 'a cmp -> 'a -> 'a list -> bool = fun cmp x ->
  let rec mem_sorted l =
    match l with
    | [] -> false
    | y :: l ->
      match cmp x y with 0 -> true | n when n > 0 -> mem_sorted l | _ -> false
  in mem_sorted

(** [insert cmp x l] inserts [x] in the list [l] assuming that [l] is sorted
   in increasing order wrt [cmp]. *)
let insert : 'a cmp -> 'a -> 'a list -> 'a list = fun cmp x ->
  let rec insert acc = function
    | y :: l' when cmp x y > 0 -> insert (y :: acc) l'
    | l -> L.rev_append acc (x :: l)
  in insert []

(* unit tests *)
let _ =
  assert
    (insert Stdlib.compare 0 [1;2;3] = [0;1;2;3]
     && insert Stdlib.compare 2 [1;2;3] = [1;2;2;3]
     && insert Stdlib.compare 4 [1;2;3] = [1;2;3;4])

(** [insert cmp x l] inserts [x] in the list [l] assuming that [l] is sorted
   in increasing order wrt [cmp], but only if [x] does not occur in [l]. *)
let insert_uniq : 'a cmp -> 'a -> 'a list -> 'a list = fun cmp x ->
  let exception Found in
  let rec insert acc l =
    match l with
    | [] -> L.rev_append acc [x]
    | y :: l' ->
        begin
          let n = cmp x y in
          match n with
          | 0 -> raise Found
          | _ when n > 0 -> insert (y :: acc) l'
          | _ -> L.rev_append acc (x :: l)
        end
  in
  fun l -> try insert [] l with Found -> l

(* unit tests *)
let _ =
  assert
    (let l = [2;4;6] in
     insert_uniq Stdlib.compare 1 l = [1;2;4;6]
     && insert_uniq Stdlib.compare 3 l = [2;3;4;6]
     && insert_uniq Stdlib.compare 7 l = [2;4;6;7]
     && insert_uniq Stdlib.compare 4 l == l)

(** [split_last l] returns [(l',x)] if [l = append l' [x]], and
@raise Invalid_argument otherwise. *)
let split_last : 'a list -> 'a list * 'a = fun l ->
  match rev l with
  | hd::tl -> (rev tl, hd)
  | [] -> invalid_arg "split_last: empty list"

(** [rev_mapi f [x1;..;xn]] returns [f (n-1) xn; ..; f 0 x1]. *)
let rev_mapi f =
  let rec aux acc i l =
    match l with
    | [] -> acc
    | x::l -> aux (f i x :: acc) (i+1) l
  in aux [] 0

(** [swap i xs] put the i-th element (counted from 0) of [xs] at the head.
@raise Invalid_argument if the i-th element does not exist. *)
let swap : int -> 'a list -> 'a list = fun i xs ->
  let rec swap acc i xs =
    match (i, xs) with
    | (0, x::xs) -> x :: rev_append acc xs
    | (i, x::xs) -> swap (x::acc) (i-1) xs
    | (_, _    ) -> invalid_arg (__LOC__ ^ "swap")
  in swap [] i xs

(** [fold_left_while f cond a [b1 b2 ..]] computes (f..(f (f a b1) b2)..bm)
where [cond] is true for b1..bm and false for b_m+1 or bm is last element *)
let rec fold_left_while f cond acc l =
  match l with
  | x :: _ when not (cond x) -> acc
  | x :: xs -> fold_left_while f cond (f acc x) xs
  | [] -> acc

(** [remove_first f l] removes from [l] the first element satisfying [f]. *)
let remove_first : ('a -> bool) -> 'a list -> 'a list = fun f ->
  let rec rem acc = function
    | [] -> rev acc
    | x::l -> if f x then rev_append acc l else rem (x::acc) l
  in rem []

(** [remove_heads n xs] remove the min(n,length xs) elements of [xs]. *)
let rec remove_heads n = function
  | _ :: xs when n > 0 -> remove_heads (n - 1) xs
  | xs -> xs

(** [split f l] returns the tuple [(l1,x,l2)] such that [x] is the first
   element of [l] satisying [f], [l1] is the sub-list of [l] preceding [x],
   and [l2] is the sub-list of [l] following [x].
@raise Not_found if there is no element of [l] satisying [f]. *)
let split : ('a -> bool) -> 'a list -> 'a list * 'a * 'a list = fun f ->
  let rec split acc = function
    | [] -> raise Not_found
    | x::m -> if f x then (L.rev acc, x, m) else split (x::acc) m
  in split []
