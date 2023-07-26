Query Language
==============

Queries can be expressed according to the following syntax:

::

   Q ::= B | Q,Q | Q;Q | Q|PATH
   B ::= WHERE HOW GENERALIZE? PATTERN
   PATH ::= << string >>
   WHERE ::= name | match | rule | lhs | rhs | type | concl | hyp | spine
   HOW ::= : | = | ~
   GENERALIZE ::= generalize
   PATTERN ::= << term possibly containing placeholders _ (for terms) and V# (for variable occurrences >>

where

* the precedence order is ``,`` > ``;`` > ``|``
* parentheses can be used as usual to force a different precedence order
* ``match`` can be paired only with ``:`` and ``name`` can be paired only with ``:`` and no ``generalize``
* a pattern should be wrapped in parentheses, unless it is atomic (e.g. an identifier or a placeholder)

The semantics of the query language is the following:

* a query ``Q`` is either a base query ``B``, the conjunction ``Q1,Q2`` of two queries ``Q1`` and ``Q2``, their disjunction ``Q1;Q2`` or the query ``Q|PATH`` that behaves as ``Q``, but only keeps the results whose path is a suffix of ``PATH`` (that must be a valid path prefix, e.g. it must not contain spaces)
* a base query ``name: ID`` looks for symbols with name ``ID`` in the library.
  The identifier ``ID`` must not be qualified.
* a base query ``WHERE HOW GENERALIZE? PATTERN`` looks in the library for occurrences of the pattern ``PATTERN`` **up to normalization rules** and, if ``generalize`` is specified, also **up to generalization** of the pattern. The normalization rules are library specific and are employed during indexing. They can be used, for example, to remove the clutter associated to encodings, to align concepts by mapping symbols to cross-library standard ones, or to standardize the shape of statements to improve recall (e.g. replacing occurrence of ``x > y`` with ``y < x``).
* ``WHERE`` restricts the set of occurrences we are interested in as follow:

  * ``match`` matches without restrictions
  * ``rule``  matches only in rewriting rules
  * ``lhs``/``rhs``  matches only in the left-hand-side/right-hand-side of rewriting rules
  * ``typ``  matches only in the type of symbols
  * ``spine`` matches only in the spine of the type of symbols, i.e. what is left of the type skipping zero or more (but not all) universal quantifications/implications
  * ``concl`` matches only in the conclusion of the type of symbols, i.e. what is left skipping all universal quantifications/implications
  * ``hyp`` matches only in the hypotheses of the type of symbols, i.e. in the type of an universal quantification/in the right left of an implication that occur in the spine

* ``HOW`` further restricts the set of occurrences we are interested in as follows, where positions have already been restricted by ``WHERE``:

  * ``:`` matches without restrictions
  * ``=`` the pattern must match the whole position
  * ``~`` the pattern must match a strict subterm of the position
