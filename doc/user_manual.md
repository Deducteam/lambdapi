Lambdapi user manual
====================

This document explains several of the concepts behind `lambdapi` and serves as
a user documentation. Installation instructions can be found in the repository
(see [README.md](README.md)). Here is a rough summary:
```bash
git clone https://github.com/Deducteam/lambdapi.git
cd lambdapi
make && make install
```

The installation of `lambdapi` gives you:
 - a main executable named `lambdapi` in your `PATH`,
 - an OCaml library called `lambdapi`,
 - an LSP-compatible server called `lp-lsp` in your `PATH`,
 - a `lambdapi` mode for `Vim` (optional),
 - a `lambdapi` mode for `emacs` (optional).

Table of contents
-----------------

 - [What is Lambdapi?](about)

 - [Command line options](options)

 - [User interfaces](ui)

 - [Module system](module)

 - [Syntax](syntax)

 - [Compatibility with Dedukti](dedukti)
 
 - [API](api)

 - [Contributing](../CONTRIBUTING)
 
 - [Compiling and profiling](devel.md)
