(** Tree constructors: a simpler representation of terms to be used by a
    decision tree. *)

open Extra

(** A constructor is the representation of a symbol along with the number of
    arguments to which it is applied. *)
type treecons =
  | Symb of
      { c_sym : Files.module_path
      (** Fully qualified name of the constructor. *)
      ; c_ari : int
      (** Arity of the considered constructor.  A same symbol representation
          may generate several constructors with different arities.  See
          [tests/OK/arity_diff.lp] for an example. *) }
  | Abst
  (** An abstraction*)
  | Vari of string
  (** A bound variable with a name. *)

(** [pp o c] prints tree constructor [c] to output channel [o]. *)
let pp : treecons pp = fun oc -> function
  | Abst    -> Format.fprintf oc "λ"
  | Vari(s) -> Format.pp_print_string oc s
  | Symb(t) -> Format.fprintf oc "%s<:%d" (List.last t.c_sym) t.c_ari

(** [compare c d] is a comparison function for constructors; more efficient
    than the pervasive. *)
let compare : treecons -> treecons -> int = fun ca cb ->
  match ca, cb with
  | Symb(a), Symb(b) ->
      begin match Int.compare a.c_ari b.c_ari with
      | 0 -> Pervasives.compare a.c_sym b.c_sym
      | x -> x
      end
  | x, y                 -> Pervasives.compare x y

(** A simple comparable type. *)
module type Comparable =
sig

  (** Type of data. *)
  type t

  (** A mapping is considered {i big} if the number of bindings exceeds the
      threshold.  The threshold [t] should be such that
      + a {!constructor:Light} mapping with [t - 1] elements should have an
        access time smaller than a {!constructor:Heavy} one,
      + a {!constructor:Heavy} mapping with [t + 1] elements should have an
        access time smaller than a {!constructor:Light} one. *)
  val threshold : int

  (** [compare x y] is [< 0] if [x < y], [= 0] if [x = y] and [> 0]
      otherwise. *)
  val compare : t -> t -> int
end

(** Subset of a mapping with {!type:constructor} as keys. *)
module type MapSig =
sig
  (** Type of keys. *)
  type key

  (** Type of a mapping. *)
  type +'a t

  (** The empty map. *)
  val empty : 'a t

  (** [is_empty m] returns whether [m] is empty; more efficient than comparing
      to [empty] (avoids a conversion). *)
  val is_empty : 'a t -> bool

  (** [add k e m] adds element [e] with key [k] to mapping [m]. *)
  val add : key -> 'a -> 'a t -> 'a t

  (** [bindings m] returns an associative list [(k, e)] with [k] key and [e]
      element. *)
  val bindings : 'a t -> (key * 'a) list

  (** [find k m] returns the element mapped by [k]
      through [m].
      @raise Not_found if [k] is not a key of [m]. *)
  val find : key -> 'a t -> 'a

  (** [iter f m] iters function [f] on mapping [m]. *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit

  (** [map f m] maps [f] on mapping m. *)
  val map : ('a -> 'b) -> 'a t -> 'b t
end

(** [MkMap(C)] creates a mapping from values of [C].  Very small mappings are
    treated differently to have faster access. *)
module MkMap(C:Comparable) : (MapSig with type key = C.t) =
struct
  module ConsMap = Map.Make(C)

  type key = C.t

  type +'a t =
    | Light of (key * 'a) list
    | Heavy of 'a ConsMap.t

  let eq : key eq = fun x y -> C.compare x y = 0

  let heavy_of_bindings : (key * 'a) list -> 'a ConsMap.t = fun x ->
    List.fold_left (fun hacc (k, e) -> ConsMap.add k e hacc) ConsMap.empty x

  let empty = Light([])
  let is_empty = function
    | Light([])      -> true
    | Light(_ :: _)  -> false
    | Heavy(x)       -> ConsMap.is_empty x
  let add k e m = match m with
    | Light(x) -> let x = (k, e) :: x in
      if List.length x > C.threshold
      then Heavy(heavy_of_bindings x) else Light(x)
    | Heavy(x) -> Heavy(ConsMap.add k e x)
  let find k = function
    | Light(x) -> List.assoc_eq eq k x
    | Heavy(x) -> ConsMap.find k x
  let bindings = function
    | Light(x) -> x
    | Heavy(x) -> ConsMap.bindings x
  let map f = function
    | Light(x) -> Light(List.map (fun (k, e) -> (k, f e)) x)
    | Heavy(x) -> Heavy(ConsMap.map f x)
  let iter f = function
    | Light(x) -> List.iter (fun (k, e) -> f k e) x
    | Heavy(x) -> ConsMap.iter f x
end

(** A mapping on {!type:treecons}. *)
module Map = MkMap(struct
    type t = treecons
    let threshold = 4
    let compare = compare end)
