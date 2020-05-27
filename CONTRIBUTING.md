Contributing to Lambdapi
========================

Contributions to `lambdapi` are very welcome!
Here are some guidelines for contributing to this project.


General style and indentation
-----------------------------

In the interest of code source uniformity, we ask that:
 - the *tabulation character should be banned*,
 - one indentation unit is equal to two spaces,
 - there should be *no trailing spaces* at the end of lines,
 - lines length should be limited to *78 characters* (excluding newline).

You can add the following lines in your .emacs to check the previous constraints:
```
(require 'whitespace)
(setq whitespace-line-column 78)
(add-hook 'tuareg-mode-hook (function (lambda () (whitespace-mode t))))
(add-hook 'lambdapi-mode-hook (function (lambda () (whitespace-mode t))))
```
and the following line to set the default Emacs window size as the maximum size of a line:
```
(add-to-list 'default-frame-alist '(width . 82))
```

You should at the very least run `make sanity_check` before committing anything.
*Please check you have GNU awk (gawk) installed* or another UTF-8 compatible
implementation of the AWK programming language interpreter.

The script `tools/git_hook_helper.sh` helps setting up a git hook to run
`make sanity_check` automatically *before* each commit.
It is encouraged to set up such a hook.
The script may be called with the `-b` option to include compilation in the
hook.

About code, **remember to break the line after `=`, if it is too long**.
You can find more details in the previous sections.

Importing of librairies
-----------------------

Import a library when you use it many times.
But to avoid problems with generic names (make, get, ...), you have to put the name of the library before the name of the function.

Naming of variables
-------------------

Type of the variable | Name of the variable
-------------------- | --------------------
       prop          |        p
       expo          |        e
       term          |        t
       sym           |
     Sig_state       |        ss
     
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
(if any), the beginning of the lines should be aligned with the first word
of the first line.
You can do the same thing for nested functions, but it's not mandatory.

Pattern matching
----------------

Pattern matching arrows should be aligned to improve readability, especially in the case where almost all of the pattern matching can be seen, as in the
following.
```ocaml
match ... with
| A(x)   -> ...
| B(x,y) -> ...
```

When the action of a pattern does not fit on one line, it should be indented
by two units (that is, four characters).
```OCaml
| A(x) ->
>>>>let y = ... in
>>>>...
```

If-then-else
------------

* If we can write the `if-then-else` instruction on one line, you should do it!
* If it is not possible, follow one of these templates:
```OCaml
if (* test *) then
>> (* first case *)
else (* second case *)
```
or, if it is not possible to write the second case on one line:
```OCaml
if (* test *) then
>> (* first case *)
else 
>> (* second case *)
```
It is not readable if the `test` statement cannot be written on one line, so you must write `if (* test *) then` on one line only.

Record
------

Please follow this template:
```OCaml
(** Description of the inductive type*)
type name =
  { constructor1 : type1  (** Description of the field 1  *)
         ...
  ; constructorN : typeN  (** Description of the field N  *) }
```
If it is not possible to write the description on one line, the template is:
```OCaml
(** Description of the inductive type*)
type name =
  { constructor1 : type1
  (** Description of the field 1  *)
         ...
  ; constructorN : typeN
  (** Description of the field N  *) }
```

Do the same thing with sum-types.

Let-in construction
-------------------

The template is very simple:
```OCaml
let (* name *) = (* ... *) in
```
or, if you need several lines:
```OCaml
let (* name *) =
 (* ... *)
in
```

Building of examples
--------------------

Don't forget to build your own examples about your job.
Moreover, the naming convention is to start the name of an object with a lowercase letter, and the name of a type with an uppercase letter.
For example:
```
// Type of natural numbers
constant symbol nat : Set
set declared "ℕ"
definition ℕ ≔ τ nat
constant symbol zero : ℕ
constant symbol succ : ℕ → ℕ

// Induction principle
symbol nat_ind p : π (p 0) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)
```