Proof tactics
=============

The ``symbol`` command allows the user to enter an interactive mode to
solve typing goals (find a term of a given type) and unification goals
(prove that two terms are equivalent). In a typing goal, the term to
find is materialized by a metavariable. The following tactics help
users to refine typing goals and transform unification goals step by
step. A tactic application may generate new
goals/metavariables. Except for the ``solve`` tactic which applies to
all the unification goals at once, all the tactics applies to the
first goal only, which is called the *focused* goal. One can change
the focus goal by using the ``focus`` tactic. The proof is complete
only when all generated goals have been solved.

Reminder: the BNF grammar of tactics is in `syntax.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/docs/syntax.bnf>`__.

``begin``
---------

Start a proof.

``focus``
---------

Put the focus on another goal. A goal is identified by its number in
the list of goals displayed by the ``print`` command. In Emacs,
clicking on the goal will add the required ``focus`` command in the
source.

``end``
-------

Exit the proof mode when all goals have been solved. It then adds in
the environment the symbol declaration or definition the proof is
about.

``abort``
^^^^^^^^^

Exit the proof mode without changing the environment.

``admitted``
^^^^^^^^^^^^

Add axioms in the environment to solve the remaining goals and exit of
the proof mode.


``apply``
---------

If ``t`` is a term of type ``Π x₁:T₁, …, Π xₙ:Tₙ,U``, then ``apply t``
refines the focused type goal with ``t _ … _`` (with n underscores).

``assume``
----------

If the focus type goal is of the form ``Π x₁ … xₙ,T``, then ``assume
h₁ … hₙ`` replaces it by ``T`` with ``xᵢ`` replaced by ``hᵢ``.

``induction``
-------------

If the focus type goal is of the form ``Π x:I …, …`` with ``I`` an
inductive type, then ``induction`` refines it by applying the
induction principle of ``I``.

``refine``
----------

The tactic ``refine t`` tries to instantiate the focused goal by the
term ``t``. ``t`` can contain references to other goals by using
``?n`` where ``n`` is a goal name. ``t`` can contain underscores ``_``
or new metavariable names ``?n`` as well. The type-checking and
unification algorithms will then try to instantiate some of the
metavariables. The new metavariables that cannot be solved are added
as new goals.

``simpl``
---------

Normalizes the focused goal with respect to β-reduction and the
user-defined rewriting rules.

``solve``
---------

Simplify unification goals as much as possible.

``why3``
--------

The tactic ``why3`` calls a prover (using the why3 platform) to solve
the current goal. The user can specify the prover in two ways :

* globally by using the command ``set prover`` described in :doc:`queries`

* locally by the tactic ``why3 "<prover_name>"`` if the user wants to change the
  prover inside an interactive mode.

If no prover name is given, then the globally set prover is used
(``Alt-Ergo`` by default).

A set of symbols should be defined in order to use the ``why3`` tactic.
The user should define those symbols using builtins as follows :

::

   set builtin "T"     ≔ T       // : U → TYPE
   set builtin "P"     ≔ P       // : Prop → TYPE
   set builtin "bot"   ≔ bot     // : Prop
   set builtin "top"   ≔ top     // : Prop
   set builtin "imp"   ≔ imp     // : Prop → Prop → Prop
   set builtin "and"   ≔ {|and|} // : Prop → Prop → Prop
   set builtin "or"    ≔ or      // : Prop → Prop → Prop
   set builtin "not"   ≔ not     // : Prop → Prop

**Important note:** you must run ``why3 config --full-config`` to make
Why3 know about the available provers.

``admit``
---------

Adds in the environment new symbols (axioms) proving the focused goal.

``fail``
^^^^^^^^

Always fails. It is useful when developing a proof to stop at some
particular point.

Tactics on equality
-------------------

The tactics ``reflexivity``, ``symmetry`` and ``rewrite`` assume the
existence of terms with approriate types mapped to the builtins ``T``,
``P``, ``eq``, ``eqind`` and ``refl`` thanks to the following builtin
declarations:

::

   set builtin "T"     ≔ … // : U → TYPE
   set builtin "P"     ≔ … // : Prop → TYPE
   set builtin "eq"    ≔ … // : Π {a}, T a → T a → Prop
   set infix … "="   ≔ eq  // optional
   set builtin "refl"  ≔ … // : Π {a} (x:T a), P (x = x)
   set builtin "eqind" ≔ … // : Π {a} x y, P (x = y) → Π p:T a→Prop, P (p y) → P (p x)

``reflexivity``
^^^^^^^^^^^^^^^

Solves a goal of the form ``P (t = u)`` when ``t ≡ u``.

``symmetry``
^^^^^^^^^^^^

Replaces a goal of the form ``P (t = u)`` by the goal ``P (u = t)``.

``rewrite``
^^^^^^^^^^^

The ``rewrite`` tactic takes as argument a term ``t`` of type
``Π x₁ … xₙ,P(l = r)`` prefixed by an optional ``left`` (to indicate that the
equation should be used from right to left) and an optional rewrite
pattern in square brackets, following the syntax and semantics of
SSReflect rewrite patterns:

::

   <rw_patt> ::=
     | <term>
     | "in" <term>
     | "in" <ident> "in" <term>
     | <ident> "in" <term>
     | <term> "in" <ident> "in" <term>
     | <term> "as" <ident> "in" <term>

See `A Small Scale Reflection Extension for the Coq
system <http://hal.inria.fr/inria-00258384>`_, by Georges Gonthier,
Assia Mahboubi and Enrico Tassi, INRIA Research Report 6455, 2016,
section 8, p. 48, for more details.

In particular, if ``u`` is a subterm of the focused goal matching ``l``,
that is, of the form ``l`` with ``x₁`` replaced by ``u₁``, …, ``xₙ``
replaced by ``uₙ``, then the tactic ``rewrite t`` replaces in the
focused goal all occurrences of ``u`` by the term ``r`` with ``x₁``
replaced by ``u₁``, …, ``xₙ`` replaced by ``uₙ``.

