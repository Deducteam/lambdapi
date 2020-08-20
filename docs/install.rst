Installation via `Opam <http://opam.ocaml.org/>`_
=================================================

The version of ``lambdapi`` that is directly available through Opam
(with the command ``opam install lambdapi``) is currently outdated. We
will only publish a new version of ``lambdapi`` Opam package when the
development has reached a more stable test. For now, we advise you to
pin the development repository to get the latest bug fixes.

.. code:: shell

   opam pin add lambdapi https://github.com/Deducteam/lambdapi.git

The installation of ``lambdapi`` gives you:

* a main executable named ``lambdapi`` in your ``PATH``,
* an OCaml library called ``lambdapi.core`` (system internals),
* an OCaml library called ``lambdapi.pure`` (pure interface),
* an OCaml library called ``lambdapi.lsp`` (LSP server),
* a ``lambdapi`` mode for ``Vim`` (optional),
* a ``lambdapi`` mode for ``emacs`` (optional).
