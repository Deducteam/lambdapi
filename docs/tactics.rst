Syntax of proof tactics
=======================

The ``theorem`` command makes the user enter an interactive mode. The
user has to provide a term of some given type. Such a goal is
materialized by a metavariable of the given type (goals and
metavariables are synonyms). One can then partially instantiate a goal
metavariable by using commands specific to this proof mode called
tactics. A tactic may generate new goals/metavariables. The proof of the
theorem is complete only when all generated goals have been solved.

Reminder: the BNF grammar of Lambdapi is in :download:`syntax.bnf`.

``print``
---------

The ``print`` command displays the list of current goals. The first one
is called the focused goal. Tactics apply to the focused goal.

``qed``
-------

The ``qed`` command allows one to quit the proof mode when all goals
have been solved. It then adds in the environment a new opaque
definition whose type is the theorem statement.

``admit``
---------

The ``admit`` command allows one to quit the proof mode even if all
goals have not been solved. It then adds in the environment a new symbol
(axiom) whose type is the theorem statement.

``abort``
---------

The ``abort`` command allows one to quit the proof mode without changing
the environment.

``focus``
---------

The ``focus`` command allows the user to change the focus to another
goal. A goal is identified by its number in the list of goals displayed
by the ``print`` command.

``simpl``
---------

The ``simpl`` tactic normalizes the focused goal with respect to
β-reduction and the user-defined rewriting rules.

``refine``
----------

The tactic ``refine t`` tries to instantiate the current goal by the
term ``t``. ``t`` can contain references to other goals by using ``?n``
where ``n`` is a goal number or a goal name. ``t`` can contain
underscores ``_`` or new metavariable names ``?n`` which will be
replaced by new metavariables. The unification and type-checking
algorithms will then try to instantiate some of the generated
metavariables. The metavariables that cannot be solved are added as new
goals.

``assume``
----------

The tactic ``assume h1 .. hn`` replaces a goal of type ``Πx1 .. xn,T``
by a goal of type ``T`` with ``xi`` replaced by ``hi``.

``apply``
---------

The tactic ``apply t`` replaces a goal of type ``T`` by possibly new
goals ``?0`` of type ``TO``, …, ``?n`` of type ``Tn`` if ``t`` is of
type ``Πx1:T1,..,Πxn:Tn,?0`` and ``t ?1 .. ?n`` is of type ``T``.

``why3``
--------

The tactic ``why3`` calls a prover (using the why3 platform) to solve
the current goal. The user can specify the prover in two ways :

* globally by using the command ``set prover`` (described in :doc:`commands`)

* locally by the tactic ``why3 "<prover_name>"`` if the user wants to change the
  prover inside an interactive mode.

If no prover name is given, then the globally set prover is used
(``Alt-Ergo`` by default).

A set of symbols should be defined in order to use the ``why3`` tactic.
The user should define those symbols using builtins as follow :

::

   set builtin "T"     ≔ T       // : U → TYPE
   set builtin "P"     ≔ P       // : Prop → TYPE
   set builtin "bot"   ≔ bot     // : Prop
   set builtin "top"   ≔ top     // : Prop
   set builtin "imp"   ≔ imp     // : Prop → Prop → Prop
   set builtin "and"   ≔ {|and|} // : Prop → Prop → Prop
   set builtin "or"    ≔ or      // : Prop → Prop → Prop
   set builtin "not"   ≔ not     // : Prop → Prop

**Important note:** you must run ``why3 config --detect`` whenever
installing a new prover supported by Why3.

Tactics on equality
-------------------

The tactics ``reflexivity``, ``symmetry`` and ``rewrite`` assume the
existence of terms with approriate types mapped to the builtins ``T``,
``P``, ``eq``, ``eqind`` and ``refl`` thanks to the following builtin
declarations:

::

   set builtin "T"     ≔ ... // : U → TYPE
   set builtin "P"     ≔ ... // : Prop → TYPE
   set builtin "eq"    ≔ ... // : Π {a}, T a → T a → Prop
   set infix ... "="   ≔ eq  // optional
   set builtin "refl"  ≔ ... // : Π {a} (x:T a), P (x=x)
   set builtin "eqind" ≔ ... // : Π {a} x y, P (x=y) → Π p:T a→Prop, P (p y) → P (p x)

``reflexivity``
---------------

The tactic ``refl`` solves a goal of the form ``P (t = u)`` when
``t ≡ u``.

``symmetry``
------------

The tactic ``sym`` replaces a goal of the form ``P (t = u)`` by the goal
``P (u = t)``.

``rewrite``
-----------

The ``rewrite`` tactic takes as argument a term ``t`` of type
``Πx1 .. xn,P(l=r)`` prefixed by an optional ``-`` (to indicate that the
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
section 8, p. 48, for more details.

In particular, if ``u`` is a subterm of the focused goal matching ``l``,
that is, of the form ``l`` with ``x1`` replaced by ``u1``, …, ``xn``
replaced by ``un``, then the tactic ``rewrite t`` replaces in the
focused goal all occurrences of ``u`` by the term ``r`` with ``x1``
replaced by ``u1``, …, ``xn`` replaced by ``un``.

``fail``
--------

The ``fail`` tactic always fails. It is useful when developing a proof
to stop at some particular point.
