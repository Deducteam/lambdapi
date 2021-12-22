`Vim <https://www.vim.org/>`__
==============================

A minimal Vim mode is provided to edit Lambdapi files. It provides
syntax highlighting and abbreviations to enter unicode characters.
It does not provide support for the LSP server yet.

Installation
------------

Installing from sources

  The Vim mode can be installed using the command
  ``make install_vim`` in the ``lambdapi`` repository.

Installing with Opam

  If Lambdapi is installed with Opam or using ``dune build`` from the
  sources, then the line

  .. code:: vim

     set rtp+=~/.opam/$OPAM_SWITCH_PREFIX/share/vim

  must be added to the Vim configuration file (``~/.vimrc`` for Vim,
  ``~/.config/nvim/init.vim`` for NeoVim).
