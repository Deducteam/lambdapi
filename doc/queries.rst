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

Each functionality is represented by a single character. To get the
list of all available debug flags, use the command ``debug`` with no
argument.

.. _flag:

``flag``
--------

Sets some flags ``on`` or ``off``, mainly for modifying the printing
behavior. Only the flag ``"eta_equality"`` changes the behavior of the
rewrite engine by reducing η-redexes. You can get the list of
available flags by using the command ``flag`` with no argument.

::

   flag "eta_equality" on; // default is off
   flag "print_implicits" on; // default is off
   flag "print_contexts" on; // default is off
   flag "print_domains" on; // default is off
   flag "print_meta_args" on; // default is off

.. _print:

``print``
---------

::

   print; // prints the current goal
   print <string_literal>; // prints the string
   print <symbol>; // prints the type, notation and rules of a symbol
   // in case of an inductive type, it also prints the associated types,
   // constructors and the recursors
   print builtin; // prints the current builtins
   print unif_rule; // prints unification rules
   print coerce_rule; // prints coercion rules
   print verbose; // prints the current verbose level
   print debug; // prints all the debug flags and their values
   print flag; // prints all the flags and their values
   print prover; // prints the current default prover
   print prover_timeout; // prints the current default timeout (in seconds)

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

Runs a query against the index file updated
with the assets defined in the file under development including the
assets imported by the `require` commands.
See :doc:`query_language` for the query language
specification.

::

  search spine >= (nat → nat) with hyp >= bool;

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
