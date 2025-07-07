Proof tactics
=============

The BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

.. _admit:

``admit``
---------

Adds in the environment new symbols (axioms) proving the focused goal.

.. _apply:

``apply``
---------

``apply t`` refines the current goal with ``t _ … _``, i.e. ``t``
applied to a number of underscores, which depends on the goal and the
type of ``t``. For instance, if ``t`` is a term of type ``Π x₁:T₁, …,
Π xₙ:Tₙ,U`` and ``U`` matches the current goal, then it will generated
``n`` subgoals for ``T₁``, …,``Tₙ``.


.. _assume:

``assume``
----------

If the focused typing goal is of the form ``Π x₁ … xₙ,T``, then
``assume h₁ … hₙ`` replaces it by ``T`` with each ``xᵢ`` replaced by
``hᵢ``.

.. _fail:

``change``
---------

``change t`` replaces the current goal ``u`` by ``t``, if ``t ≡ u``.

``fail``
--------

Always fails. It is useful when developing a proof to stop at some
particular point.

.. _generalize:

``generalize``
--------------

If the focused goal is of the form ``x₁:A₁, …, xₙ:Aₙ, y₁:B₁, …, yₚ:Bₚ
⊢ ?₁ : U``, then ``generalize y₁`` transforms it into the new goal
``x₁:A₁, …, xₙ:Aₙ ⊢ ?₂ : Π y₁:B₁, …, Π yₚ:Bₚ, U``.

.. _have:

``have``
--------

``have x: t`` generates a new goal for ``t`` and then let the user prove
the focused typing goal assuming ``x: t``.

.. _induction:

``induction``
-------------

If the focused goal is of the form ``Π x:I …, …`` with ``I`` an
inductive type, then ``induction`` refines it by applying the
induction principle of ``I``.

.. _refine:

``refine``
----------

The tactic ``refine t`` tries to instantiate the focused goal by the
term ``t``. ``t`` can contain references to other goals by using
``?n`` where ``n`` is a goal name. ``t`` can contain underscores ``_``
or new metavariable names ``?n`` as well. The type-checking and
unification algorithms will then try to instantiate some of the
metavariables. The new metavariables that cannot be solved are added
as new goals.

.. _remove:

``remove``
----------

``remove h₁ … hₙ`` erases the hypotheses ``h₁ … hₙ`` from the context of the current goal.
The remaining hypotheses and the goal must not depend directly or indirectly on the erased hypotheses.
The order of removed hypotheses is not relevant.

.. _set:

``set``
-------

``set x ≔ t`` extends the current context with ``x ≔ t``.

.. _simplify:

``simplify``
------------

With no argument, ``simplify`` normalizes the focused goal with respect
to β-reduction and the user-defined rewriting rules.

``simplify rule off`` normalizes the focused goal with respect to
β-reduction only.

If ``f`` is a non-opaque symbol having a definition (introduced with
``≔``), then ``simplify f`` replaces in the focused goal every occurrence
of ``f`` by its definition.

If ``f`` is a symbol identifier having rewriting rules, then ``simplify
f`` applies these rules bottom-up on every occurrence of ``f`` in the
focused goal.

.. _solve:

``solve``
---------

Simplify unification goals as much as possible.

.. _why3:

``why3``
--------

The tactic ``why3`` calls a prover (using the why3 platform) to solve
the current goal. The user can specify the prover in two ways :

* globally by using the command ``prover`` described in :doc:`queries`

* locally by the tactic ``why3 "<prover_name>"`` if the user wants to change the
  prover inside an interactive mode.

If no prover name is given, then the globally set prover is used
(``Alt-Ergo`` by default).

A set of symbols should be defined in order to use the ``why3`` tactic.
The user should define those symbols using builtins as follows :

::

   builtin "T"   ≔ … // : U → TYPE
   builtin "P"   ≔ … // : Prop → TYPE
   builtin "bot" ≔ … // : Prop
   builtin "top" ≔ … // : Prop
   builtin "not" ≔ … // : Prop → Prop
   builtin "and" ≔ … // : Prop → Prop → Prop
   builtin "or"  ≔ … // : Prop → Prop → Prop
   builtin "imp" ≔ … // : Prop → Prop → Prop
   builtin "eqv" ≔ … // : Prop → Prop → Prop
   builtin "all" ≔ … // : Π x: U, (T x → Prop) → Prop
   builtin "ex"  ≔ … // : Π x: U, (T x → Prop) → Prop

**Important note:** you must run ``why3 config detect`` to make
Why3 know about the available provers.
