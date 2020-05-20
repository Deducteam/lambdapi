User interfaces
---------------

A prototype language server is provided with Lambdapi. It follows (an extension
of) the [LSP protocol](https://microsoft.github.io/language-server-protocol/),
which is supported by most editors. See below for setting up common editors.

The server is run using the command `lambdapi lsp`. The flag `--standard-lsp`
can be use to enforce strict LSP protocol (without extensions targeted at
logical formalizations).

### VSCode

There is an extension for VSCode >= 1.37 derived from VSCoq. To
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

_note_: as of today the vscode mode requires a full lambdapi install,
it won't unfortunately run from a developer tree.

### Emacs

The `emacs` mode is automatically installed during lambdapi installation
via `make` . Support for the LSP server is enabled by default,  but
it requires the [eglot](https://github.com/joaotavora/eglot) plugin to be
installed (using `M-x package-install eglot RET` should work).

To enter unicode symbols using Latex commands, one can for instance use
[company-math](https://github.com/vspinu/company-math).

Note that `eglot` does not support the extended protocol information sent by
our LSP server yet.

### Vim

The `Vim` mode can be installed optionally using the command `make install_vim`
in the `lambdapi` repository. It does not have support for the LSP server yet.

### Atom

Support for the `Atom` editor exists but is deprecated.

See [atom-dedukti](https://github.com/Deducteam/atom-dedukti) for instructions
related to the `Atom` editor.
