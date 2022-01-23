open Base

type 'a t = 'a option

let is_None : 'a t -> bool = fun o ->
  match o with None -> true | Some _ -> false

let get : 'a -> 'a option -> 'a = fun d o ->
  match o with None -> d | Some e -> e

let map : ('a -> 'b) -> 'a t -> 'b t = fun f o ->
  match o with None -> None | Some e -> Some (f e)

let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b = fun f d o ->
  match o with None -> d | Some e -> f e

let bind : ('a -> 'b t) -> 'a t -> 'b t = fun f o ->
  match o with None -> None | Some e -> f e

let iter : ('a -> unit) -> 'a t -> unit = fun f o ->
  match o with None -> () | Some e -> f e

let fold : ('a -> 'b -> 'a) -> 'a -> 'b option -> 'a = fun f a o ->
  match o with None -> a | Some b -> f a b

let cmp : 'a cmp -> 'a option cmp = fun cmp_elt o o' ->
  match o, o' with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some x, Some x' -> cmp_elt x x'

let eq : 'a eq -> 'a option eq = fun eq_elt o1 o2 ->
  match o1, o2 with
  | None, None -> true
  | Some e1, Some e2 -> eq_elt e1 e2
  | _ -> false

let pp : 'a pp -> 'a option pp = fun elt ppf o ->
  match o with None -> () | Some e -> elt ppf e
