Implementation choices
----------------------

- Back-tracking in interactive proofs is implemented using the “timed”
  references of the `Timed`_ library.

- Bindings in terms are implemented using the `Bindlib`_ library.

- Parsing uses the `Menhir`_ library.

.. _Timed: https://github.com/rlepigre/ocaml-timed
.. _Bindlib: https://rlepigre.github.io/ocaml-bindlib/
.. _Menhir: http://gallium.inria.fr/~fpottier/menhir/
