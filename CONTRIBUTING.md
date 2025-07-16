Contributing to Lambdapi
========================

Contributions to `lambdapi` are very welcome!
Here are some guidelines for contributing to this project.

For contributing to the VSCode extension, see
`editors/vscode/INSTALL.md` and `editors/vscode/CONTRIBUTING.md`.

For contributing to the User Manual, see `doc/README.md`.

Branching and pull-request policy
---------------------------------

Lambdapi uses only one branch, `master`. Releases are tagged.

Contributions to Lambdapi should be done by doing pull-requests from
your forked repo of Lambdapi. Pull-requests are then reviewed,
commented and eventually merged.

- If the file structure is changed, `doc/structure.rst` should be changed as well.
- Important contributions should update the file `CHANGES.md`.

General style and indentation
-----------------------------

In the interest of code source uniformity, we require:
 - do not use tabulation characters
 - one indentation unit is equal to two spaces,
 - there should be no trailing spaces at the end of lines,
 - line length should be limited to 78 characters excluding newline
   (except for `@see` commands for `ocamldoc`)

You should run `make sanity_check` before committing anything. The
script `misc/git_hook_helper.sh` helps setting up a git hook to run
`make sanity_check` automatically before each commit. The script may
be called with the `-b` option to include compilation in the hook.
Please check that you have GNU awk (gawk) installed or another UTF-8
compatible implementation of the AWK programming language interpreter.

Naming convention
-----------------

No plural forms in filenames, type names or module names (e.g. file
term.ml and not terms.ml, type term and not terms).

For OCaml identifiers, we use the snake_case naming convention.

In Lambdapi files, objects should start with a lowercase letter while
types should start with an uppercase letter.

Type annotations and interface files
------------------------------------

Lambdapi does not use many interface (or `.mli`) files. However, every function
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
- `editors/vim/syntax/lambdapi.vim`
- `editors/emacs/lambdapi-vars.el` (syntax coloring)
- `editors/emacs/lambdapi-smie.el` (grammar and indentation)
- `editors/vscode/lp.configuration.json` (comments configuration),
- `editors/vscode/syntaxes/lp.tmLanguage.json` (syntax highlighting),
- `misc/lambdapi.tex`
- `doc/Makefile.bnf`
- `doc/lambdapi.bnf` by doing `make bnf`
- the User Manual files in the `doc/` repository (do `make doc` to generate and check the Sphynx documentation).

Adding a tactic
---------------

When adding a tactic in Lambdapi, make sure to update the following files:
- the type `tactic` in `src/core/tactic.ml`
- `doc/tacticals.rst`
- `tests/OK/Tactic.lp`
