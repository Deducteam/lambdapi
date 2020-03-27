## Protocol For Logical Formalizations

This directory contains a prototype language server for the λΠ logical
framework. At this stage, this is a very experimental prototype, use
with care.

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
