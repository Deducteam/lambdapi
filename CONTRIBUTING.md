Contributing to Lambdapi
========================

Here are a few guidelines for contributing to this project.


Directories and files
---------------------

 * `src`: source code of Lambdapi

   + utilities:
   
     - extra: standard library extension
     - files: filenames and paths management
     - console: output and debugging utilities

   + file, command and tactic handling:
   
     - lambdapi: main file
     - compile: file parsing and compiling (.lpo files)
     - handle: command handling
     - tactics: tactic handling
     - rewrite: rewrite tactic
     - proof: proof state

   + terms, signatures, rewriting, unification and type-checking:
   
     - terms: internal representation of terms
     - basics: basic operations on terms
     - print: pretty printing of terms
     - eval: rewriting engine
     - solve: unification algorithm
     - ctxt: typing contexts (maps variable -> type)
     - typing: type-checking algorithm
     - sign: signatures/theories (sets of symbols and rules)

   + parsing and scoping:
   
     - pos: source file position management
     - syntax: abstract syntax
     - parser: parser (convert the concrete syntax into the abstract syntax)
     - env: maps identifier -> variable (and type)
     - scope: convert the abstract syntax into terms
     - pretty: pretty print the abstract syntax (used to convert old Dedukti files into Lambdapi files)

   + legacy parser:
   
     - legacy_lexer: lexer for the old Dedukti syntax
     - legacy_parser: interface of the parser for the old Dedukti syntax
     - menhir_parser: parser using Menhir (http://gallium.inria.fr/~fpottier/menhir/)

   + property checking:
   
     - sr: algorithm for checking subject reduction
     - confluence: call confluence checker by converting signatures into a TRS file

   + interface to editors:
   
     - pure: interface to the LSP server

 * lp-lsp: source code of the Lambdapi LSP server (see https://microsoft.github.io/language-server-protocol/ and https://langserver.org/)

 * tests: unit tests
   - OK: tests that should succeed
   - KO: tests that should fail

 * examples: examples of Dedukti or Lambdapi files with no proofs

 * proofs: examples of Lambdapi files with proofs

 * tools:
   - deps.ml:
   - lambdapi.tex: listings setup for including Lambdapi code in Latex
   - sanity_check.sh: script checking some style guidelines below (called by `make sanity_check`)

 * libraries: libraries of Dedukti files (see GNUmakefile)


General style and indentation
-----------------------------

In the interest of code source uniformity, we ask that:
 - the *tabulation character should be banned*,
 - one indentation unit is equal to two spaces,
 - there should be *no trailing spaces* at the end of lines,
 - lines length should be limited to *78 characters* (excluding newline).

You should at the very least run `make sanity_check` before comiting anything.


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

When the action of a pattern does not fit on one line, it sould be indented
by two units (that is, four characters).
```OCaml
| A(x) ->
>>>>let y = ... in
>>>>...
```
