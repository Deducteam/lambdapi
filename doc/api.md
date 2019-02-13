### Lambdapi OCaml library

The `lambdapi` OCaml library gives access to the core data structures that are
used by `lambdapi`. It can be used to experiment with the type-checker and the
rewriting engine of `lambdapi`, but also to propose new (compatible) tools. It
is currently used by the implementation of the LSP server (next section).

### Lambdapi LSP server

The `lambdapi` LSP server, called `lp-lsp`, implements an interface to editors
supporting the [LSP](https://github.com/Microsoft/language-server-protocol)
protocol. For now,  we support the `emacs` editor through the `eglot` package,
and also the `Atom` editor with a custom plugin.

See the file [lp-lsp/README.md](lp-lsp/README.md) for more details.
