## Protocol For Logical Formalizations

This directory contains a prototype language server for the λΠ logical
framework. At this stage, this is a very experimental prototype, use
with care.

## Using with VSCode

There is an extension for VSCode derived from VSCoq. To install do:

```bash
cd editors/vscode/
npm install
ln -s `pwd` ~/.vscode/extensions/
```

You need a recent enough VSCode (>= 1.31)

## Using with Emacs

Lambdapi LSP server will work out of the box with emacs and eglot,
to do so, install [eglot](https://github.com/joaotavora/eglot)
[using `M-x package-install eglot RET` should work], then do
`M-x eglot` and specify as a server `lambdapi --lsp-server --standard-lsp`.

`eglot` doesn't support the extended protocol information sent by
Lambdapi LSP server yet.

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
- `Lsp_doc`: Document model for LP documents.
- `Lsp_lsp`: Main server, command handlers.
