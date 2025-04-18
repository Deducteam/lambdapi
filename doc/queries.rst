Queries
=======

.. _assert:
.. _assertnot:

``assert``, ``assertnot``
-------------------------

The ``assert`` and ``assertnot`` are convenient for checking that the
validity, or the invalidity, of typing judgments or equivalences.
This can be used for unit testing of Lambdapi, with both positive and
negative tests.

::

   assert ⊢ zero : Nat;
   assert ⊢ add (succ zero) zero ≡ succ zero;
   assertnot ⊢ zero ≡ succ zero;
   assertnot ⊢ succ : Nat;

.. _compute:

``compute``
-----------

Computes the normal form of a term.

.. _debug:
   
``debug``
---------

The user can activate (with ``+``) or deactivate (with ``-``) the
debug mode for some functionalities as follows:

::

   debug +ts;
   debug -s;

Each functionality is represented by a single character. For instance,
``i`` stands for type inference. To get the list of all debuggable
functionalities, run the command ``lambdapi check --help``.

.. _flag:

``flag``
--------

Sets some flags ``on`` or ``off``, mainly for modifying the printing
behavior. Only the flag ``"eta_equality"`` changes the behavior of the
rewrite engine by reducing η-redexes.

::

   flag "eta_equality" on; // default is off
   flag "print_implicits" on; // default is off
   flag "print_contexts" on; // default is off
   flag "print_domains" on; // default is off
   flag "print_meta_types" on; // default is off
   flag "print_meta_args" on; // default is off

.. _print:

``print``
---------

When called with a symbol identifier as argument, displays information
(type, notation, rules, etc.) about that symbol. When called with
``unif_rule`` as argument, displays the list of unification
rules. When called with ``coerce_rule`` as argument, displays the list
of coercions. Without argument, displays the list of current goals (in
proof mode only).

.. _proofterm:

``proofterm``
-------------

Outputs the current proof term (in proof mode only).

.. _prover:

``prover``
----------

Changes the prover used by the ``why3`` tactic. By default, it uses
*Alt-Ergo*.

::

   prover "Eprover";

.. _prover_timeout:
   
``prover_timeout``
------------------

Changes the timeout (in seconds) for the ``why3`` tactic. At the
beginning, the timeout is set to 2s.

::

   prover_timeout 60;

.. _search_cmd:

``search``
------------------

Runs a query between double quotes against the index file
``~/.LPSearch.db``. See :doc:`query_language` for the query language
specification.

::

  search "spine >= (nat → nat) , hyp >= bool";

.. _type:

``type``
--------

Returns the type of a term.

.. _verbose:

``verbose``
-----------

Takes as argument a non-negative integer. Higher is the verbose
level, more details are printed. At the beginning, the verbose is set
to 1.

::

   verbose 3;
