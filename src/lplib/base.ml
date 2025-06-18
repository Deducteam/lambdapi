(** Standard library extension (mostly). *)

(** Type of pretty-printing functions. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

let out = Format.fprintf
let std = Format.std_formatter

let (++) (p1: 'a pp) (p2: 'b pp) : ('a * 'b) pp = fun ppf (arg1, arg2) ->
  out ppf "%a%a" p1 arg1 p2 arg2

let (|+) p1 p2 : 'a pp = fun ppf arg -> (p1 ++ p2) ppf ((), arg)
let (+|) p1 p2 : 'a pp = fun ppf arg -> (p1 ++ p2) ppf (arg, ())

let int : int pp = Format.pp_print_int
let char : char pp = Format.pp_print_char
let string : string pp = Format.pp_print_string
let float : float pp = fun ppf -> out ppf "%f"
let unit : unit outfmt -> unit pp = fun fmt ppf () -> out ppf fmt
let sep : string -> unit pp = fun s ff () -> string ff s

let pp_if : bool -> 'a pp -> 'a pp = fun b pp ppf arg ->
  if b then out ppf "%a" pp arg

let prefix : string -> 'a pp -> 'a pp = fun s pp ppf x ->
  out ppf "%s%a" s pp x
let suffix : 'a pp -> string -> 'a pp = fun pp s ppf x ->
  out ppf "%a%s" pp x s

(** Type of comparison functions. *)
type 'a cmp = 'a -> 'a -> int

(** Comparison function through a map. *)
let cmp_map : 'b cmp -> ('a -> 'b) -> 'a cmp = fun cmpb f a1 a2 ->
  cmpb (f a1) (f a2)

(** Tag comparison function. *)
let cmp_tag : 'a cmp = fun t t' ->
  cmp_map Stdlib.compare (fun t -> Obj.tag (Obj.repr t)) t t'

(** Lexicographic comparison. *)
let lex : 'a cmp -> 'b cmp -> ('a * 'b) cmp = fun cmpa cmpb (a1,b1) (a2,b2) ->
  match cmpa a1 a2 with
  | 0 -> cmpb b1 b2
  | n -> n

let lex3 : 'a cmp -> 'b cmp -> 'c cmp -> ('a * 'b * 'c) cmp =
  fun cmpa cmpb cmpc (a1,b1,c1) (a2,b2,c2) ->
  lex cmpa (lex cmpb cmpc) (a1,(b1,c1)) (a2,(b2,c2))

(** Type of equality functions. *)
type 'a eq = 'a -> 'a -> bool

let eq_of_cmp : 'a cmp -> 'a eq = fun cmp x y -> cmp x y = 0

module Int = struct
  type t = int
  let compare = ( - )
end
