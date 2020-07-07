User interfaces
---------------

A prototype language server is provided with Lambdapi. It follows (an
extension of) the `LSP
protocol <https://microsoft.github.io/language-server-protocol/>`__,
which is supported by most editors. See below for setting up common
editors.

The server is run using the command ``lambdapi lsp``. The flag
``--standard-lsp`` can be use to enforce strict LSP protocol (without
extensions targeted at logical formalizations).

.. toctree::
   :caption: Contents:

   emacs.rst
   vscode.rst
   vim.rst
   atom.rst
