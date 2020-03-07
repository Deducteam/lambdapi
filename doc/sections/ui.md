User interfaces
---------------

A prototype language server is provided with Lambdapi. It follows (an extension
of) the Language Server Protocol (LSP), which is supported by most editors. See
below for setting up your favorite editor.

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

### Emacs

The `emacs` mode can be optionally installed using `make install_emacs` in the
`lambdapi` repository.  Support for the LSP server is enabled by default,  but
it requires the [eglot](https://github.com/joaotavora/eglot) plugin to be
installed (using `M-x package-install eglot RET` should work).

To enter unicode symbols using Latex commands, one can for instance use
[company-math](https://github.com/vspinu/company-math).

Note that `eglot` does not support the extended protocol information sent by
our LSP server yet.

### Vim

The `Vim` mode can be installed similarly using the command `make install_vim`
in the `lambdapi` repository. It does not have support for the LSP server yet.

### Atom

Support for the `Atom` editor exists but is deprecated.

See [atom-dedukti](https://github.com/Deducteam/atom-dedukti) for instructions
related to the `Atom` editor.
