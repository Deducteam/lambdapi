Lambdapi- Implementation of the λΠ-calculus modulo rewriting
============================================================

Lambdapi is an implementation of the λΠ-calculus modulo rewriting, which
is the system of Dedukit (https://github.com/Deducteam/Dedukti).

Dependencies and compilation
----------------------------

Lambdapi requires a Unix-like system. It should work on Linux as well as on
MacOS. It might also be possible to make it work on Windows with Cygwyn or
with "bash on Windows").

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

Tests and supported libraries
-----------------------------

You can run tests with:
 - `make unit_tests` (small tests also run by `make`)
 - `make tests` (many more small tests)
 - `make matita` (type-checks Matita's arithmetic library)

Tests for more libraries are also provided. Use the following commands and
follow the instructions (only the first time):
 - `make focalide`
 - `make holide`
 - `make verine`
 - `make iProverModulo`
