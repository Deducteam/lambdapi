open Base

type 'a t = 'a option

let map : ('a -> 'b) -> 'a t -> 'b t =
 fun f o -> match o with None -> None | Some e -> Some (f e)

let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b =
 fun f d o -> match o with None -> d | Some e -> f e

let iter : ('a -> unit) -> 'a t -> unit =
 fun f o -> match o with None -> () | Some e -> f e

let get : 'a -> 'a option -> 'a =
 fun d o -> match o with None -> d | Some e -> e

let equal : 'a eq -> 'a option eq =
 fun eq o1 o2 ->
  match (o1, o2) with
  | None, None -> true
  | Some e1, Some e2 -> eq e1 e2
  | _, _ -> false

(** [pp pp_elt oc o] prints on the channel [oc] the element [e] with [pp_elt] if
    [o = Some e]. *)
let pp : 'a pp -> 'a option pp =
 fun pp_elt oc o -> match o with None -> () | Some e -> pp_elt oc e

let empty x = match x with | None -> true | Some _ -> false
let default x d = match x with | None -> d | Some x -> x

let fold : ('a -> 'b -> 'a) -> 'a -> 'b option -> 'a = fun f a o ->
  match o with
  | None -> a
  | Some b -> f a b

(** Total order on option types. *)
let cmp_option : 'a cmp -> 'a option cmp = fun cmp o o' ->
  match o, o' with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some x, Some x' -> cmp x x'
