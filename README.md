Lambdapi- Implementation of the λΠ-calculus modulo rewriting
============================================================

Lambdapi is an implementation of the λΠ-calculus modulo rewriting, which
is the system of Dedukit (https://github.com/Deducteam/Dedukti).

Dependencies and compilation
----------------------------

List of dependencies:
 - GNU make,
 - OCaml (at least 4.02.0),
 - ocamlbuild,
 - findlib,
 - bindlib (from source https://github.com/rlepigre/ocaml-bindlib)
 - earley (from source https://github.com/rlepigre/ocaml-earley)
 - earley-ocaml (from source https://github.com/rlepigre/ocaml-earley-ocaml)

To compile Lambdapi, just run the command `make` in the source directory.
This produces the `lambdapi.native` binary, which can be run on files with
the `.dk` extension (use `./lambdapi.native --help` for more informations).
