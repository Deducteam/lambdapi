Proof tactics on equality
=========================

The BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

The tactics ``reflexivity``, ``symmetry`` and ``rewrite`` assume the
existence of terms with approriate types mapped to the builtins ``T``,
``P``, ``eq``, ``eqind`` and ``refl`` thanks to the following builtin
declarations:

::

   builtin "Set"   ≔ … // : TYPE
   builtin "T"     ≔ … // : Set → TYPE
   builtin "Prop"  ≔ … // : TYPE
   builtin "P"     ≔ … // : Prop → TYPE
   builtin "eq"    ≔ … // : Π [a], T a → T a → Prop
   builtin "refl"  ≔ … // : Π [a] (x:T a), P(x = x)
   builtin "eqind" ≔ … // : Π [a] x y, P(x = y) → Π p:T a → Prop, P(p y) → P(p x)

Application of the ``rewrite`` tactic to terms depending on enclosing
bound variables additionally relies on the following builtin
declarations:

::

   builtin "arr"    ≔ … // : Set → Set → Set
   builtin "funExt" ≔ … // : Π [a b] (f g: T (arr a b)), (Π x: T a, P(f x = g x)) → P(f = g)

.. _reflexivity:

``reflexivity``
---------------

Solves a goal of the form ``Π x₁, …, Π xₙ, P (t = u)`` when ``t ≡ u``.

.. _rewrite:

``rewrite``
-----------

The ``rewrite`` tactic takes as argument a term ``t`` of type ``Π x₁ …
xₙ,P(l = r)`` prefixed by an optional ``left`` (to indicate that the
equation should be used from right to left) and an optional rewrite
pattern in square brackets prefixed by a dot, following the syntax and
semantics of SSReflect rewrite patterns:

::

   <rw_patt> ::=
     | <term>
     | "in" <term>
     | "in" <ident> "in" <term>
     | <ident> "in" <term>
     | <term> "in" <ident> "in" <term>
     | <term> "as" <ident> "in" <term>

See examples in `rewrite1.lp <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/rewrite1.lp>`_
and `A Small Scale Reflection Extension for the Coq
system <http://hal.inria.fr/inria-00258384>`_, by Georges Gonthier,
Assia Mahboubi and Enrico Tassi, INRIA Research Report 6455, 2016,
section 8, p. 48, for more details.

In contrast to SSReflect, ``rewrite`` allows can target terms
depending on bound variables (justified by functional extensionality),
and supports rewrite patterns containing binders. For examples, see `rewrite_under_binders.lp <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/rewrite_under_binders.lp>`_.

In particular, if ``u`` is a subterm of the focused goal matching ``l``,
that is, of the form ``l`` with ``x₁`` replaced by ``u₁``, …, ``xₙ``
replaced by ``uₙ``, then the tactic ``rewrite t`` replaces in the
focused goal all occurrences of ``u`` by the term ``r`` with ``x₁``
replaced by ``u₁``, …, ``xₙ`` replaced by ``uₙ``.
For occurrences depending on enclosing bound variables, replacement is
restricted to instances referring to the same enclosing binders as the
first match.

.. _symmetry:

``symmetry``
------------

Replaces a goal of the form ``P (t = u)`` by the goal ``P (u = t)``.
