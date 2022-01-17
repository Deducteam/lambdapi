open Common
open Term

let coerce : sym =
  let id = Pos.none "#c" in
  Sign.add_symbol Ghost.sign Public Defin Eager false id mk_Kind []

let is_coercion : sym -> bool = (==) coerce

(** [apply t a b] creates the coercion of [t] from [a] to [b]. *)
let apply : term -> term -> term -> term = fun t a b ->
  add_args (mk_Symb coerce) [a; t; b]
