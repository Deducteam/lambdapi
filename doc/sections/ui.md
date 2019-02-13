### Emacs mode

The `emacs` mode can be optionally installed using `make install_emacs` in the
`lambdapi` repository.  Support for the LSP server is enabled by default,  but
it requires the `eglot` plugin to be installed.

See the file [../../lp-lsp/README.md](lp-lsp/README.md) for more details.

### Vim mode

The `Vim` mode can be installed similarly using the command `make install_vim`
in the `lambdapi` repository. It does not yet have support for the LSP server.

### Atom mode

Support for the `Atom` editor exists,  but is deprecated since the editor will
most certainly disappear in the near future (in favor of `VS Code`).

See [atom-dedukti](https://github.com/Deducteam/atom-dedukti) for instructions
related to the `Atom` editor.
