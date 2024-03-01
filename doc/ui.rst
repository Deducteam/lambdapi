User interfaces
---------------

Lambdapi provides a language server for (an extension of) the `LSP
protocol`_, which is supported by most editors. See below for setting
up common editors.

The server is run using the command ``lambdapi lsp``. The flag
``--standard-lsp`` can be used to enforce strict LSP protocol and, thus,
currently, deactivate goal display.

.. toctree::
   :maxdepth: 1

   emacs.rst
   vscode.rst
   vim.rst (not maintained anymore)

.. _LSP protocol: https://microsoft.github.io/language-server-protocol/
