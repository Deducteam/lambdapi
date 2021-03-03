Contributing to Lambdapi
========================

Contributions to `lambdapi` are very welcome!
Here are some guidelines for contributing to this project.

For contributing to the User Manual, see `docs/README.md`.

Branching and pull-request policy
---------------------------------

The Github repo has a branch for each release and the `master` branch
for the development of the next release.

Contributions to Lambdapi should be done by using pull-requests on
Github. You should first clone Lambdapi on Github, create a branch for
your contribution, push it and, then, make a pull-request from the
Github web interface. Pull-requests are then reviewed, commented and
eventually merged.

- If the file structure is changed, `docs/structure.rst` should be changed as
  well.
- Important contributions should update the file `CHANGES.md`.

General style and indentation
-----------------------------

In the interest of code source uniformity, we ask that:
 - the *tabulation character should be banned*,
 - one indentation unit is equal to two spaces,
 - there should be *no trailing spaces* at the end of lines,
 - line length should be limited to *78 characters* excluding newline
   (except for `@see` commands for `ocamldoc`).

You should at the very least run `make sanity_check` before committing
anything. The script `tools/git_hook_helper.sh` helps setting up a
git hook to run `make sanity_check` automatically *before* each
commit. It is encouraged to set up such a hook. The script may be
called with the `-b` option to include compilation in the hook.
Please check that you have GNU awk (gawk) installed or another UTF-8
compatible implementation of the AWK programming language interpreter.

Naming convention
-----------------

For OCaml identifiers, we use the snake_case naming convention.

In Lambdapi files, objects should start with a lowercase letter while
types should start with an uppercase letter.

Type annotations and interface files
------------------------------------

Lambdapi does not use interface (or `.mli`) files. However, every function
should be documented with its type, and an `ocamldoc` comment. We ask that
the type of a function is given with the following syntax:
```ocaml
(** [a_function x y z] does some things with [x], [y] and [z]. *)
let a_function : int -> (bool -> bool) -> string -> unit = fun x y z ->
  ...
```

Changing the syntax of Lambdapi
-------------------------------

When changing the syntax of Lambdapi, make sure to update the
following files:
- `src/core/lpLexer.ml`
- `src/core/lpParser.mly`
- `src/core/pretty.ml`
- `src/core/print.ml`
- `editors/emacs/lambdapi-smie.el`
- `editors/vscode/lp.configuration.json` (comments configuration),
- `editors/vscode/syntaxes/lp.tmLanguage.json` (syntax highlighting),
- `tools/listings.tex`
- `docs/Makefile` (generation of `docs/syntax.bnf`)
- as well as the User Manual in the `docs/` repository.
