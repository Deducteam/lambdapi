See the file [lp-lsp/README.md](../../lp-lsp/README.md) for more details.

### VSCode

There is an extension for VSCode 1.37 derived from VSCoq. To
install it do from the `lambdapi` repository:

```bash
cd editors/vscode/
make clean
make
```

This requires to have `npm` and `node-typescript` installed:

```bash
sudo apt install npm node-typescript
```

### Emacs

The `emacs` mode can be optionally installed using `make install_emacs` in the
`lambdapi` repository.  Support for the LSP server is enabled by default,  but
it requires the `eglot` plugin to be installed.

To enter unicode symbols using Latex commands, one can for instance use [company-math](https://github.com/vspinu/company-math).

### Vim

The `Vim` mode can be installed similarly using the command `make install_vim`
in the `lambdapi` repository. It does not have support for the LSP server.

### Atom

Support for the `Atom` editor exists but is deprecated.

See [atom-dedukti](https://github.com/Deducteam/atom-dedukti) for instructions
related to the `Atom` editor.
