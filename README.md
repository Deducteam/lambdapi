Lambdapi, a proof assistant based on the λΠ-calculus modulo rewriting <!--[![Gitter][gitter-badge]][gitter-link] [![Matrix][matrix-badge]][matrix-link]-->
=====================================================================

``>>>>>`` [User Manual](https://lambdapi.readthedocs.io) ``<<<<<``
------------------------------------------------------------------

Issues can be reported on the
[issue tracker](https://github.com/Deducteam/lambdapi/issues).

Questions can be asked on the
[forum](https://github.com/Deducteam/lambdapi/discussions).

User interfaces
---------------

- [Emacs](https://lambdapi.readthedocs.io/en/latest/emacs.html)
- [VSCode](https://lambdapi.readthedocs.io/en/latest/vscode.html)

Libraries
---------

Lambdapi libraries can be found on the [Opam repository of Lambdapi libraries](https://github.com/Deducteam/opam-lambdapi-repository).

Examples
--------

- [tutorial](https://raw.githubusercontent.com/Deducteam/lambdapi/master/tests/OK/tutorial.lp) (learn Lambdapi in 15 minutes)
- [some logic definitions](https://github.com/Deducteam/lambdapi-logics)
- [inductive-recursive type definition](https://github.com/Deducteam/lambdapi/blob/master/tests/OK/indrec.lp)
- [inductive-inductive type definition](https://github.com/Deducteam/lambdapi/blob/master/tests/OK/indind.lp)
- [library on natural numbers, integers and polymorphic lists](https://github.com/Deducteam/lambdapi-stdlib)

Some users
----------

- [Stephan Merz](https://members.loria.fr/Stephan.Merz/) and [Alessio Coltellacci](https://github.com/NotBad4U): certification of [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) proofs
- [Claude Stolze](https://perso.eleves.ens-rennes.fr/people/claude.stolze/): certification of [Atelier B](https://www.atelierb.eu/) proofs
- [Jean-Paul Bodeveix](https://www.irit.fr/~Jean-Paul.Bodeveix/): certification of [Rodin](http://www.event-b.org/platform.html) proofs for Event-B
- [Simon Guilloud](https://people.epfl.ch/simon.guilloud): certification of [LISA](https://github.com/epfl-lara/lisa) proofs
- Thomas Traversié: [An Implementation of Set Theory with Pointed Graphs](https://hal.inria.fr/hal-03740004)
- [Quentin Garchery](https://www.lri.fr/~garchery/): certification of [Why3](http://why3.lri.fr/) proof task transformations

Operating systems
-----------------

Lambdapi requires a Unix-like system. It should work on Linux as well as on
MacOS. It might be possible to make it work on Windows too with Cygwin or
"bash on Windows".

Installation via Opam
---------------------

```bash
opam install lambdapi
```
gives you the command ``lambdapi``.

The [Emacs](https://lambdapi.readthedocs.io/en/latest/emacs.html) extension is available on [MELPA](https://melpa.org/#/lambdapi-mode).

The [VSCode](https://lambdapi.readthedocs.io/en/latest/vscode.html) extension is available on the [Marketplace](https://marketplace.visualstudio.com/items?itemName=Deducteam.lambdapi).

To browse the source code documentation, you can do:
```bash
opam install odig
odig doc lambdapi
```

To install Lambdapi libraries, see the [opam-lambdapi-repository](https://github.com/Deducteam/opam-lambdapi-repository).

**Remark:** To install Opam, see [here](https://opam.ocaml.org/).

To make sure that programs installed via opam are in your path, you
should have in your `.bashrc` (or any other shell initial file) the
following line that can be automatically added when you do `opam
init`:

```bash
test -r ~/.opam/opam-init/init.sh && . ~/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true
```

To update your path, you can also do:
```bash
eval `opam env`
```

Compilation from the sources
----------------------------

You can get the sources using `git` as follows:
```bash
git clone https://github.com/Deducteam/lambdapi.git
```

Dependencies are described in `lambdapi.opam`. The command `why3
config detect` must be run for Why3 to know the available provers for
the `why3` tactic.

Using Opam, a suitable OCaml environment can be setup as follows:
```bash
cd lambdapi
opam install .
why3 config detect
```

To compile Lambdapi, just run the command `make` in the source directory.
This produces the `_build/install/default/bin/lambdapi` binary.
Use the `--help` option for more information. Other make targets are:

```bash
make                        # Build lambdapi
make doc                    # Build the user documentation (avalaible on readthedocs)
make bnf                    # Build the BNF grammar
make odoc                   # Build the developer documentation
make install                # Install lambdapi
make install_emacs_mode     # Install emacs mode
make install_vim_mode       # Install vim mode
```

You can run `lambdapi` without installing it with `dune exec -- lambdapi`.

For running tests, one also needs
[alcotest](https://github.com/mirage/alcotest) and
[alt-ergo](https://alt-ergo.ocamlpro.com/).

For building the source code documentation, one needs
[odoc](https://github.com/ocaml/odoc). The starting file of the source
code html documentation is
`_build/default/_doc/_html/lambdapi/index.html`.

For building the User Manual, see `doc/README.md`.

The following commands can be used to clean up the repository:
```bash
make clean     # Removes files generated by OCaml.
make distclean # Same as clean, but also removes library checking files.
make fullclean # Same as distclean, but also removes downloaded libraries.
```

<!--
[gitter-badge]: https://badges.gitter.im/Deducteam/lambdapi.svg
[gitter-link]: https://gitter.im/Deducteam/lambdapi
[matrix-badge]: http://strk.kbt.io/tmp/matrix_badge.svg
[matrix-link]: https://riot.im/app/#/room/#lambdapi:matrix.org
-->
