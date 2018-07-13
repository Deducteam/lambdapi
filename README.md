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
 - bindlib 5.0.0 (https://github.com/rlepigre/ocaml-bindlib),
 - earley 1.0.2 (https://github.com/rlepigre/ocaml-earley),
 - earley-ocaml 1.0.2 (https://github.com/rlepigre/ocaml-earley-ocaml).
 - timed 1.0 (https://github.com/rlepigre/ocaml-timed).

Using Opam, a suitable OCaml environment can be setup as follows.
```bash
opam switch 4.05.0
eval `opam config env`
opam install ocamlfind ocamlbuild
opam install bindlib.5.0.0 earley.1.0.2 earley-ocaml.1.0.2 timed.1.0
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
 - `make tests`        (unit tests)
 - `make matita`       (type-checks Matita's arithmetic library)
 - `make plein_de_dks` (type-checks many random files)
 - `make focalide`     (type-checks the Focalide library)
 - `make holide`       (type-checks the Holide library)
 - `make verine`       (type-checks the Verine library)
 - `make iprover`      (type-checks the iProverModulo library)
 - `make dklib`        (type-checks the dklib library)
 - `make zenon`        (type-checks the zenon library)

Repository organization
-----------------------

The root directory of the repository contains several folders:
 - `editors` holds the files related to editor support (Vim only for now),
 - `examples` holds a bunch of examples (taken from Dedukti and new ones),
 - `libraries` holds the scripts used for checking supported libraries,
 - `src` contains the source code of Lambdapi,
 - `tests` contains test files (mostly from Dedukti),
 - `tools` contains miscellaneous utility scripts.
