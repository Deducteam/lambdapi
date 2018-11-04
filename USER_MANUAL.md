Lambdapi user manual
====================

This document explains several of the concepts behind `lambdapi` and serves as
a user documentation. Installation instructions can be found in the repository
(see [README.md](README.md)). Here is a rough summary:
```bash
git clone https://github.com/rlepigre/lambdapi.git
cd lambdapi
make && make install
```

What is Lambdapi?
-----------------

The `lambdapi` system is several things!

### A logical framework

The core (theoretical) system of `lambdapi` is a logical framework based on the
λΠ-calculus modulo rewriting. In other words, it is dependent type theory that
is somewhat similar to Martin-Lőf's dependent type theory  (i.e., an extension
of the λ-calculus) but that has the peculiarity of allowing the user to define
function symbols with associated rewriting rules. Although the system seems to
be very simple at first, it is surprisingly powerful. In particular, it allows
the encoding of the theories behind Coq or HOL.

### A tool for interoperability of proof systems

The ability to encode several rather different systems make of `lambdapi` (and
its predecessor `Dedukti`) an ideal target for proof interoperability. Indeed,
one can for example export a proof written in Matita (an implementation of the
calculus of inductive constructions) to the OpenTheory format (shared  between 
several implementations of HOL).

### An interactive proof system

Being aimed at interoperability, `Dedukti` was never intended to become a tool
for writing proofs directly. On the contrary, `lambdapi` is aimed at providing
an interactive proof mechanism, while remaining compatible with `Dedukti` (and
its interoperability capabilities).

Here is a list of new features brought by `lambdapi`:
 - a new syntax suitable for proof developments (including tactics),
 - support for unicode (UTF-8) and (user-defined) infix operators,
 - automatic resolution of dependencies,
 - a simpler, more reliable and fully documented implementation,
 - more reliable operations on binders tanks to the Bindlib library,
 - a general notion of metavariables, useful for implicit arguments.

### An experimental proof system

Finally, let us note that `lambdapi` is to be considered (at least for now) as
an experimental proof system based on the λΠ-calculus modulo rewriting.  It is
aimed at exploring (and experimenting with)  the many possibilities offered by
rewriting, and the associated notion of conversion. In particular, it leads to
simple proofs, where many details are delegated to the conversion rule.

Although the language may resemble Coq at a surface level, it is fundamentally
different in the way mathematics can be encoded. It is yet unclear whether the
power of rewriting will be a significant advantage of `lambdapi` over  systems
like Coq. That is something that we would like to clarify (in the near future)
thanks to `lambdapi`.

Command line flags and tools
----------------------------

The installation of `lambdapi` give you:
 - a main executable named `lambdapi` in your `PATH`,
 - an OCaml library called `lambdapi`,
 - an LSP-compatible server called `lp-lsp` in your `PATH`,
 - a `lambdapi` mode for `Vim` (optional),
 - a `lambdapi` mode for `emacs` (optional).

### Main Lambdapi program

The `lambdapi` executable is the main program. It can be used to process files
written in the `lambdapi` syntax (with the ".lp" extension), and files written
in the legacy (Dedukti) syntax (with the ".dk" extension).

<!-- TODO -->

### Lambdapi OCaml library

The `lambdapi` OCaml library gives access to the core data structures that are
used by `lambdapi`. It can be used to experiment with the type-checker and the
rewriting engine of `lambdapi`, but also to propose new (compatible) tools. It
is currently used by the implementation of the LSP server (next section).

### Lambdapi LSP server

The `lambdapi` LSP server, called `lp-lsp`, implements an interface to editors
supporting the LSP standard. Limitations in the LSP protocol may require us to
consider a non-standard extension for the proof mode. For now,  we support the
`emacs` editor through the `eglot` plugin for interactive proof,  and also the
`Atom` editor with a custom plugin.

See the file [lp-lsp/README.md](lp-lsp/README.md) for more details.

### Emacs mode

The `emacs` mode can optionally (and automatically) installed with the command
`make install_emacs` in the `lambdapi` repository.  Support for the LSP server
is enabled by default, and requires the `eglot` plugin.

See the file [lp-lsp/README.md](lp-lsp/README.md) for more details.

### Vim mode

The `Vim` mode can optionally (and automatically) installed using the  command
`make install_vim` in the `lambdapi` repository. It does not yet have built-in
support for the LSP server.

### Atom mode

Support for the `Atom` editor exists,  but is deprecated since the editor will
most certainly disappear in the near future (in favor of `VS Code`).

See [atom-dedukti](https://github.com/Deducteam/atom-dedukti) for instructions
related to the `Atom` editor.

Compilation and module system
-----------------------------

<!-- TODO -->

Syntax of Lambdapi
------------------

<!-- TODO -->

Interactive proof system
------------------------

<!-- TODO -->

Compatibility with Dedukti
--------------------------

<!-- TODO -->
