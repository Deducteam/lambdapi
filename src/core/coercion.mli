open Term

val coerce : sym
(** Symbol of the function that computes coercions. Coercion rules are added
    on that symbol. *)

val apply : term -> term -> term -> term
(** [apply a b t] creates the coercion of term [t] from type [a] to type
    [b]. *)
