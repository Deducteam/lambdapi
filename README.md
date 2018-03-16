Lambdapi- Implementation of the λΠ-calculus modulo rewriting
============================================================

Lambdapi is an implementation of the λΠ-calculus modulo rewriting, which
is the system of Dedukti (https://github.com/Deducteam/Dedukti).

Dependencies and compilation
----------------------------

Lambdapi requires a Unix-like system. It should work on Linux as well as on
MacOS. It might also be possible to make it work on Windows with Cygwyn or
with "bash on Windows").

List of dependencies:
 - GNU make,
 - OCaml (at least 4.04.0),
 - ocamlbuild,
 - findlib,
 - bindlib (from opam or https://github.com/rlepigre/ocaml-bindlib),
 - earley (from opam or https://github.com/rlepigre/ocaml-earley),
 - earley-ocaml (from opam or https://github.com/rlepigre/ocaml-earley-ocaml).

Using Opam, a suitable OCaml environment can be setup as follows.
```bash
opam switch 4.05.0
eval `opam config env`
opam install ocamlfind ocamlbuild bindlib earley earley-ocaml
```

To compile Lambdapi, just run the command `make` in the source directory.
This produces the `lambdapi.native` binary, which can be run on files with
the `.dk` extension (use `./lambdapi.native --help` for more informations).

```bash
make
make install     # optionally install the program.
make install_vim # optionally install vim support.
```

Tests and supported libraries
-----------------------------

You can run tests with:
 - `make tests`    (unit tests)
 - `make matita`   (type-checks Matita's arithmetic library)
 - `make focalide` (type-checks the Focalide library)
 - `make holide`   (type-checks the Holide library)
 - `make verine`   (type-checks the Verine library)
 - `make iprover`  (type-checks the iProverModulo library)
 - `make dklibr`   (type-checks the dklib library)
 - `make zenon`   (type-checks the zenon library)
