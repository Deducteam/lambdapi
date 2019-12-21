(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Short name for the type of a comparison function. *)
type 'a cmp = 'a -> 'a -> int

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

    let is_substring : string -> string -> bool = fun e s ->
      let len_e = String.length e in
      let len_s = String.length s in
      let rec is_sub i =
        if len_s - i < len_e then false else
        if String.sub s i len_e = e then true else
        is_sub (i+1)
      in
      is_sub 0

    let for_all : (char -> bool) -> string -> bool = fun p s ->
      let len_s = String.length s in
      let rec for_all i = i >= len_s || (p s.[i] && for_all (i+1)) in
      for_all 0
  end

module Option =
  struct
    type 'a t = 'a option

    let map : ('a -> 'b) -> 'a t -> 'b t = fun f o ->
      match o with
      | None    -> None
      | Some(e) -> Some(f e)

    let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b = fun f d o ->
      match o with
      | None    -> d
      | Some(e) -> f e

    let iter : ('a -> unit) -> 'a t -> unit = fun f o ->
      match o with
      | None    -> ()
      | Some(e) -> f e

    let get_default : 'a -> 'a option -> 'a = fun d o ->
      match o with
      | None    -> d
      | Some(e) -> e

    let get : 'a option -> 'a = fun o ->
      match o with
      | None    -> assert false
      | Some(e) -> e

    let equal : 'a eq -> 'a option eq = fun eq o1 o2 ->
      match (o1, o2) with
      | (None    , None    ) -> true
      | (Some(e1), Some(e2)) -> eq e1 e2
      | (_       , _       ) -> false

    (** [pp pp_elt oc o] prints on the channel [oc] the element [e] with
        [pp_elt] if [o = Some e]. *)
    let pp : 'a pp -> 'a option pp = fun pp_elt oc o ->
      match o with
      | None   -> ()
      | Some e -> pp_elt oc e
  end

module List =
  struct
    include List

    (** [pp pp_elt sep oc l] prints the list [l] on the channel [oc] using
        [sep] as separator, and [pp_elt] for printing the elements. *)
    let pp : 'a pp -> string -> 'a list pp = fun pp_elt sep oc l ->
      match l with
      | []    -> ()
      | e::es -> let fn e = Format.fprintf oc "%s%a" sep pp_elt e in
                 pp_elt oc e; iter fn es

    (** [filter_map f l] applies [f] to the elements of [l] and keeps the [x]
        such that [Some(x)] in [List.map f l]. *)
    let rec filter_map : ('a -> 'b option) -> 'a list -> 'b list = fun f ->
      function
      | []     -> []
      | h :: t ->
          match f h with
          | Some(x) -> x :: filter_map f t
          | None    -> filter_map f t

    (** [filteri_map f l] applies [f] element wise on [l] and keeps [x] such
        that for [e] in [l], [f e = Some(x)]. *)
    let filteri_map : (int -> 'a -> 'b option) -> 'a list -> 'b list =
      fun f l ->
        let rec loop k = function
          | [] -> []
          | h :: t ->
              match f k h with
              | Some(x) -> x :: loop (succ k) t
              | None    -> loop (succ k) t
        in
        loop 0 l

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

    (** [max ?cmp l] finds the max of list [l] with compare function [?cmp]
        defaulting to [Pervasives.compare].
        @raise Invalid_argument if [l] is empty. *)
    let max : ?cmp:('a -> 'a -> int) -> 'a list -> 'a =
      fun ?(cmp=Pervasives.compare) li ->
      match li with
      | []   -> invalid_arg "Extra.List.max"
      | h::t -> let max e1 e2 = if cmp e1 e2 >= 0 then e1 else e2 in
                List.fold_left max h t

    (** [assoc_eq e k l] is [List.assoc k l] with equality function [e].
        @raise Not_found if [k] is not a key of [l]. *)
    let assoc_eq : 'a eq -> 'a -> ('a * 'b) list -> 'b = fun eq k l ->
      let rec loop l =
        match l with
        | []                      -> raise Not_found
        | (x, e) :: _ when eq x k -> e
        | _      :: t             -> loop t
      in
      loop l

    (** [remove_phys_dups l] uniqify list [l] keeping only the last element,
        using physical equality. *)
    let rec remove_phys_dups : 'a list -> 'a list = fun l ->
      match l with
      | []      -> []
      | x :: xs -> let xs = remove_phys_dups xs in
                   if List.memq x xs then xs else x :: xs

    (** [deconstruct l i] returns a triple [(left_rev, e, right)] where [e] is
        the [i]-th element of [l], [left_rev] is the reversed prefix of [l] up
        to its [i]-th element (excluded),  and [right] is the remaining suffix
        of [l] (starting at its [i+1]-th element).
        @raise Invalid_argument when [i < 0].
        @raise Not_found when [i ≥ length v]. *)
    let destruct : 'a list -> int -> 'a list * 'a * 'a list = fun e i ->
      if i < 0 then invalid_arg "Extra.List.deconstruct" ;
      let rec destruct l i r =
        match (r, i) with
        | ([]  , _) -> raise Not_found
        | (v::r, 0) -> (l, v, r)
        | (v::r, i) -> destruct (v :: l) (i - 1) r
      in
      destruct [] i e

    (** [reconstruct left_rev l right] concatenates (reversed) [left_rev], [l]
        and [right].  This function will typically be used in combination with
        {!val:deconstruct} to insert a sublist [l] in the place of the element
        at the specified position in the specified list. *)
    let reconstruct : 'a list -> 'a list -> 'a list -> 'a list = fun l m r ->
      List.rev_append l (m @ r)

    (** [init n f] creates a list with [f 0] up to [f n] as its elements. Note
        that [Invalid_argument] is raised if [n] is negative. *)
    let init : int -> (int -> 'a) -> 'a list = fun n f ->
      if n < 0 then invalid_arg "Extra.List.init" else
      let rec loop k = if k > n then [] else f k :: loop (k + 1) in loop 0

    (** [in_sorted cmp x l] tells whether [x] is in [l] assuming that [l] is
       sorted wrt [cmp]. *)
    let in_sorted : 'a cmp -> 'a -> 'a list -> bool = fun cmp x ->
      let rec in_sorted l =
        match l with
        | [] -> false
        | y :: l ->
            match cmp x y with
            | 0 -> true
            | n when n > 0 -> in_sorted l
            | _ -> false
      in in_sorted

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

    (** [pp pp_elt sep oc a] prints the array list [a] on the channel [oc]
        using [sep] as separator, and [pp_e] for printing the elements. *)
    let pp : 'a pp -> string -> 'a array pp = fun pp_elt sep oc a ->
      let n = Array.length a in
      if n > 0 then pp_elt oc a.(0);
      for i=1 to n-1 do Format.fprintf oc "%s%a" sep pp_elt a.(i) done

    (** [equal eq a1 a2] tests the equality of [a1] and [a2],  comparing their
        elements with [eq]. *)
    let equal : 'a eq -> 'a array eq = fun eq a1 a2 ->
      Array.length a1 = Array.length a2 && for_all2 eq a1 a2

    (** [max_index ?cmp a] returns the index of the first maximum of array [a]
        according to comparison [?cmp].  If [cmp] is not given, defaults to
        [Pervasives.compare]. *)
    let max_index : ?cmp:('a -> 'a -> int) -> 'a array -> int =
      fun ?(cmp=Pervasives.compare) arr ->
      let len = Array.length arr in
      if len = 0 then invalid_arg "Extra.Array.max_index" else
      let max = ref 0 in
      for i = 1 to len - 1 do
        if cmp arr.(!max) arr.(i) < 0 then max := i
      done; !max

    (** [max ?cmp a] returns the higher element according to comparison
        function [?cmp], using [Pervasives.compare] if not given, in array
        [a]. *)
    let max : ?cmp:('a -> 'a -> int)-> 'a array -> 'a =
      fun ?(cmp=Pervasives.compare) arr -> arr.(max_index ~cmp:cmp arr)

    (** [split a] is [List.split (Array.to_list a)]. *)
    let split : ('a * 'b) array -> 'a list * 'b list = fun a ->
      let aux (el, er) (accl, accr) = (el :: accl, er :: accr) in
      Array.fold_right aux a ([], [])

    (** [drop n a] discards the first [n] elements of [a].  The empty array is
        returned if [n > length a]. *)
    let drop : int -> 'a array -> 'a array = fun n a ->
      let l = length a in
      if n >= l then [||] else Array.sub a n (l - n)

  end

(** Functional maps with [int] keys. *)
module IntMap = Map.Make(Int)

(** Functional sets of integers. *)
module IntSet = Set.Make(Int)

(** Functional maps with [string] keys. *)
module StrMap = Map.Make(String)

(* Functional sets of strings. *)
module StrSet = Set.Make(String)

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
