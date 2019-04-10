(** Tree constructors. *)

open Extra

(** A constructor is the representation of a symbol along with the number of
    arguments to which it is applied. *)
type treecons =
  { c_mod : string list
  (** Module name where the symbol of the constructor is defined. *)
  ; c_sym : string
  (** Symbol of the constructor. *)
  ; c_ari : int
  (** Arity of the considered constructor.  A same symbol representation may
      generate several constructors with different arities. *) }

(** [tc_compare c d] is a comparison function for constructors; more efficient
    than the pervasive. *)
let tc_compare : treecons -> treecons -> int = fun ca cb ->
  match String.compare ca.c_sym cb.c_sym with
  | 0 ->
    begin match Int.compare ca.c_ari cb.c_ari with
      | 0 -> Pervasives.compare ca.c_mod cb.c_mod
      | x -> x
    end
  | x -> x

(** [tc_eq c d] returns true iff [c] and [d] are equal regarding
    [tc_compare]. *)
let tc_eq : treecons eq = fun a b -> tc_compare a b = 0

module type TcMapSig =
sig
  (** Type of keys. *)
  type key = treecons

  (** Type of a mapping. *)
  type 'a t

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

  (** [find_opt k m] returns [Some(e)] with [e] the element mapped by [k]
      through [m] and [None] if [k] is not in [m]. *)
  val find_opt : key -> 'a t -> 'a option

  (** [iter f m] iters function [f] on mapping [m]. *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit

  (** [map f m] maps [f] on mapping m. *)
  val map : ('a -> 'b) -> 'a t -> 'b t
end

(** Implementation of a mapping with {!type:constructor} as keys.  Very small
    mappings are treated differently.  The incentive is to have faster
    evaluation on very simple rules. *)
module TcMap : TcMapSig =
struct
  module TC = struct
    type t = treecons
    let compare = tc_compare
  end
  module ConsMap = Map.Make(TC)

  type key = treecons

  type 'a t =
    | Light of (treecons * 'a) list
    | Heavy of 'a ConsMap.t

  let heavy_of_bindings : (key * 'a) list -> 'a ConsMap.t = fun x ->
    ConsMap.of_seq @@ List.to_seq x

  (** A mapping is considered {i big} if the number of bindings exceeds the
      threshold.  The threshold [t] should be such that
      + a {!constructor:Light} mapping with [t - 1] elements should have an
        access time smaller than a {!constructor:Heavy} one,
      + a {!constructor:Heavy} mapping with [t + 1] elements should have an
        access time smaller than a {!constructor:Light} one. *)
  let threshold = 4

  let empty = Light([])
  let is_empty = function
    | Light([])      -> true
    | Light(_ :: _)  -> false
    | Heavy(x)       -> ConsMap.is_empty x
  let add k e m = match m with
    | Light(x) -> let x = (k, e) :: x in
      if List.length x > threshold
      then Heavy(heavy_of_bindings x) else Light(x)
    | Heavy(x) -> Heavy(ConsMap.add k e x)
  let find_opt k = function
    | Light(x) -> List.assoc_eq tc_eq k x
    | Heavy(x) -> ConsMap.find_opt k x
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
