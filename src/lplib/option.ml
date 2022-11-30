open Base

include Stdlib.Option

type 'a t = 'a option

let is_None : 'a t -> bool = fun o ->
  match o with None -> true | Some _ -> false

let get : 'a -> 'a option -> 'a = fun d o ->
  match o with None -> d | Some e -> e

let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b = fun f d o ->
  match o with None -> d | Some e -> f e

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

module Monad = struct
  let ( let* ) = Stdlib.Option.bind

  (** Monadic [let*] allows to replace
      {[
        match e1 with
        | Some e2 -> Some (f e2)
        | None -> None
      ]}
      with
      {[
        let* x = e1 in
        f x
      ]} *)

  let return x = Some x
end

module Applicative = struct
  let pure x = Some x
  let ( <*> ) : ('a -> 'b) option -> 'a option -> 'b option = fun o x ->
    match o with
    | Some f -> map f x
    | None -> None
end
