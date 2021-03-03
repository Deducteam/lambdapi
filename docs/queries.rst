Queries
=======

``print``
---------

When called with a symbol identifier as argument, displays information
(type, notation, rules, etc.) about that symbol. Without argument,
displays the list of current goals (in proof mode only).

``proofterm``
-------------

Outputs the current proof term (in proof mode only).

``type``
--------

Returns the type of a term.

``compute``
-----------

Computes the normal form of a term.

``assert`` and ``assertnot``
----------------------------

The ``assert`` and ``assertnot`` are convenient for checking that the
validity, or the invalidity, of typing judgments or equivalences.
This can be used for unit testing of Lambdapi, with both positive and
negative tests.

::

   assert zero : Nat;
   assert add (succ zero) zero ≡ succ zero;
   assertnot zero ≡ succ zero;
   assertnot succ : Nat;

``set verbose|debug|flag|prover|prover_timeout``
------------------------------------------------

The ``set`` command is used to control the behaviour of Lambdapi and
extension points in its syntax.

**verbose level** The verbose level can be set to an integer between 0
and 3. Higher is the verbose level, more details are printed.

::

   set verbose 1;

**debug mode** The user can activate (with ``+``) or deactivate (with
``-``) the debug mode for some functionalities as follows:

::

   set debug +ts;
   set debug -s;

Each functionality is represented by a single character. For instance,
``i`` stands for type inference. To get the list of debuggable
functionalities, run the command ``lambdapi check --help``.

**flags** The user can set/unset some flags:

::

   set flag "eta_equality" on; // default is off
   set flag "print_implicits" on; // default is off
   set flag "print_contexts" on; // default is off
   set flag "print_domains" on; // default is off
   set flag "print_meta_types" on; // default is off

**prover config**: In order to use the ``why3`` tactic, a prover should
be set using:

::

   set prover "Eprover";

*Alt-Ergo* is set by default if the user didn’t specify a prover.

The user can also specify the timeout (in seconds) of the prover:

::

   set prover_timeout 60;

The default time limit of a prover is set to 2 seconds.
