Syntax of terms
===============

The BNF grammar of Lambdapi is in :download:`syntax.bnf`.

Identifiers
-----------
A qualified identifier is an identifier of the form
``dir1.`` … ``dirn.file.id`` denoting the function symbol ``id`` defined
in the file ``dir1/`` … ``/dirn/file.lp``. To be used, ``dir1.`` …
``dirn.file`` must be required first.

An identifier can be:

*  an ASCII sequence of characters in the regular language
   ``[a-zA-Z_][a-zA-Z0-9_]*``

*  a non-negative integer if the builtins “0” and “+1” have been
   previously set (see the command ``set builtin`` in :doc:`commands`)

*  a unicode character previously declared using the command
   ``set declared``

*  an arbitrary sequence of characters enclosed between ``{|`` and
   ``|}``

Convention:
  identifiers starting with a capital letter denote types and predicates (e.g.
  ``Nat``, ``List``), and identifiers starting with a small letter denote
  constructors, functions and proofs (e.g. ``zero``, ``add``, ``refl``).

Terms
-----
A user-defined term can be either:

* ``TYPE``

* a possibly qualified identifier denoting either:

   * a qualified symbol or a non-qualified symbol previously declared in the
     current file or in some previously open module, possibly prefixed by ``@``
     to disallow implicit arguments
   * a bound variable
   * a metavariable or goal when prefixed by ``?``

* an anonymous function ``λ(x:A) y z,t`` mapping ``x``, ``y`` and ``z``
  (of type ``A`` for ``x``) to ``t``

* a dependent product ``Π(x:A) y z,T``

* a non-dependent product ``A → T`` (syntactic sugar for ``Πx:A,T`` with ``x``
  not occurring in ``T``)

* a ``let f (x:A) y z: T ≔ t in`` construction (with ``let f x : A ≔ t in u``
  being a syntactic sugar for ``let f : Πx:_ → A ≔ λx, t in u``)

* application is written by space-separated juxtaposition, except for
  symbol identifiers declared as infix (e.g. ``x+y``)

* a meta-variable application ``?M[t;u;v]``. ``?M`` alone, without arguments
  between square brackets, is a shorthand for ``?M[x1;..;xn]`` where
  ``x1;..;xn`` are all the variables of the context.

* a pattern-variable application ``$P[x;y]`` (in rules only). ``$P``
  alone, without arguments between square brackets, is a shorthand for
  ``$P[]``. This short-hand is not allowed under binders.

* ``_`` for an unknown term or a term we don’t care about. It is replaced by a
  fresh metavariable (or a fresh pattern variable in a rule left-hand side)
  applied to all the variables of the context.

* an integer between 0 and 2^30-1 if the builtins “0” and “+1” are defined (see
  the ```set`` <commands.md>`__ command)

Subterms can be parenthesized to avoid ambiguities.

In case of the application of a function symbol, an implicit argument
can be given by enclosing it between curly brackets ``{`` … ``}``.
