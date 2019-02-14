## Protocol For Logical Formalizations

This directory contains a prototype language server for the λΠ logical
framework. At this stage, this is a very experimental prototype, use
with care.

To build:

```
opam install dune cmdliner yojson
dune build
```

The resulting binary will be in `../_build/install/default/bin/lp-lsp`

## Using with VSCode

There is an extension for VSCode derived from VSCoq. To install do:

$ cd editors/vscode/
$ npm install
$ ln -s `pwd` ~/.vscode/extensions/

You need a recent enough VSCode (>= 1.31)

## Using with Emacs

`lp-lsp` will work out of the box with emacs and eglot, to do so,
install [eglot](https://github.com/joaotavora/eglot) [using `M-x
package-install eglot RET` should work], then do `M-x eglot` and
specify as a server `lp-lsp --std`.

`eglot` doesn't support the extended protocol information sent by
`lp-lsp` yet.

## Development TODO

### Phase 1: Basic document checking.

+ Re-implement document traversal.
+ Incremental checking.

### Phase 2: Basic interactive proofs

The goal of this phase is to add support for basic interaction with
λΠ, this will done by means of a query language that will support
goals, search, typeof, etc...

### Phase 3: Advanced UI support

In this phase we will provide some more advanced features for large
scale proof editing. In particular:

+ holes / incomplete proofs
+ diff management

## Structure of the server.

The server is split in 3 components:

- `Lsp_*`: Files dealing with LSP structures.
- `Lp_doc`: Document model for LP documents.
- `Lp_lsp`: Main server, command handlers.
