Contributing to Lambdapi
========================

Here are a few guidelines for contributions.


General style and indentation
-----------------------------

In the interest of code source uniformity, we ask that:
 - the *tabulation character should be banned*,
 - one indentation unit is equal to two spaces,
 - there should be *no trailing spaces* at the end of lines,
 - lines length should be limited to *78 characters* (excluding newline).


Type annotations and interface
------------------------------

Lambdapi does not use interface (or `.mli`) files. However, every function
should be documented with its type, and an `ocamldoc` comment. We ask that
the type of function is given with the following syntax (except for parsers
defined in `src/parser.ml`).
```ocaml
(** [a_function x y z] does some things with [x], [y] and [z]. *)
let a_function : int -> (bool -> bool) -> string -> unit = fun x y z ->
  ...
```

Note that `ocamldoc` comments should take up as much space as possible,
without exceeding the maximum line width. Starting at their second line
(if any), the begining of the lines should be aligned with the first word
of the first line.


Other conventions
-----------------

Pattern matching arrows should be aligned to improve readability, as in the
following.
```ocaml
match ... with
| A(x)   -> ...
| B(x,y) -> ...
```

When the action of a patter does not fit on one line, it sould be indented
by two unite (that is, four characters).
```OCaml
| A(x) ->
>>>>let y = ... in
>>>>...
```
