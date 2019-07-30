(** Encoding of the position of a subterm. *)
open Extra

(** Each element of the list is a path in the tree of the term.  For instance,
    in the term [Appl(Appl(f, x), Appl(Appl(g, a), b))], the subterm [a] has
    position [1.0], encoded by [[0 ; 1]], [b] has [1.1] encoded by [[1 ; 1]]
    and [x] has [0] encoded by [[0]]. *)
type t = int list

(** [compare a b] implements lexicographic order on positions. *)
let compare : t -> t -> int = fun a b ->
  Pervasives.compare (List.rev a) (List.rev b)

(** [pp o p] output position [p] to channel [o]. *)
let pp : t pp = fun oc pos ->
  if pos = [] then Format.fprintf oc "ε" else
  List.pp (fun oc -> Format.fprintf oc "%d") "." oc (List.rev pos)

(** Initial position. *)
let empty : t = []

(** [succ p] returns the successor of position [p].  For instance, if
    [p = [1 ; 1]], [succ p = [2 ; 1]].  The succ of the initial position is
    the first subterm of this position. *)
let succ : t -> t = fun p ->
  match p with
  | []     -> 0 :: empty
  | i :: p -> succ i :: p

(** [prefix p q] sets position [p] as prefix of position [q], for instance,
    {i prefix 1 3.4} is {i 1.3.4}; which is represented [prefix [1] [4;3]]
    is [[4;3;1]]. *)
let prefix : t -> t -> t = fun p q -> q @ p

(** [args_of a r] returns the occurrences of the arguments of root [r]
    considering it has arity [a]. *)
let args_of : int -> t -> t list = fun a r ->
  if a = 0 then [] else List.init (a - 1) (fun i -> i :: r)

(** [sub p] returns the position of the first subterm of [p]. *)
let sub : t -> t = fun p -> 0 :: p
