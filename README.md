Lambdapi- Implementation of the λΠ-calculus modulo rewriting
============================================================

Lambdapi is an implementation of the λΠ-calculus modulo rewriting, which
is the system of Dedukti (https://github.com/Deducteam/Dedukti). More details
are given in the [user manual](USER_MANUAL.md)

Installation via Opam
---------------------

See http://opam.ocaml.org/.

```bash
opam install lambdapi
```

Dependencies and compilation
----------------------------

Lambdapi requires a Unix-like system. It should work on Linux as well as on
MacOS. It might also be possible to make it work on Windows with Cygwyn or
with "bash on Windows".

List of dependencies:
 - GNU make,
 - OCaml (at least 4.04.1),
 - Dune (at least 1.2.0),
 - odoc (for documentation only),
 - bindlib 5.0.0 (https://github.com/rlepigre/ocaml-bindlib),
 - earley 1.1.0 (https://github.com/rlepigre/ocaml-earley),
 - earley-ocaml 1.1.0 (https://github.com/rlepigre/ocaml-earley-ocaml).
 - timed 1.0 (https://github.com/rlepigre/ocaml-timed).
 - menhir
 - yojson
 - cmdliner
 - ppx\_inline\_test

Using Opam, a suitable OCaml environment can be setup as follows.
```bash
opam switch 4.05.0
eval `opam config env`
opam install dune odoc menhir yojson cmdliner
opam install bindlib.5.0.0 timed.1.0 earley.1.1.0 earley-ocaml.1.1.0
```

To compile Lambdapi, just run the command `make` in the source directory.
This produces the `_build/install/default/bin/lambdapi` binary, which can
be run on files with the `.dk` or `.lp` extension (use the `--help` option
for more information).

```bash
make               # Build lambdapi.
make doc           # Build the documentation.
make install       # Install the program.
make install_vim   # Install vim support.
make install_emacs # Install emacs (>= 26.1) support (needs the eglot package)
```

**Note:** you can run `lambdapi` with `dune exec lambdapi`.

The following commands can be used for cleaning up the repository:
```bash
make clean     # Removes files generated by OCaml.
make distclean # Same as clean, but also removes library checking files.
make fullclean # Same as distclean, but also removes downloaded libraries.
```

Tests and supported libraries
-----------------------------

You can run tests using the following commands.
```bash
make tests        # Unit tests (not stopping on failure).
make real_tests   # Unit tests (stopping on first failure).

make dklib        # Checks files at https://github.com/rafoo/dklib/
make focalide     # Checks files generated from the Focalize library
make holide       # Checks files generated from the OpenTheory library
make matita       # Checks the traduction of Matita's arithmetic library.
make verine       # Checks files generated by the VeriT prover.
make iprover      # Checks files generated by iProverModulo.
make zenon_modulo # Checks files generated by ZenonModulo.
```
