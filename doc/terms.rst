Syntax of terms
===============

The BNF grammar of Lambdapi is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

Identifiers
-----------
A qualified identifier is an identifier of the form
``dir1.`` … ``dirn.file.id`` denoting the function symbol ``id`` defined
in the file ``dir1/`` … ``/dirn/file.lp``. To be used, ``dir1.`` …
``dirn.file`` must be required first.

An identifier can be:

* a regular identifier, that is, an arbitrary non-empty sequence of
  UTF-8 codepoints that are not among ``\t\r\n :,;`(){}[]".@$|?``

* an escaped identifier, that is, an arbitrary (non-empty) sequence of
  characters enclosed between ``{|`` and ``|}``

* an escaped notation identifier, that is, an identifier previously
  declared as notation, wrapped in parentheses (this allows access to
  the notationless value of the identifier)

* a non-negative integer if the builtins “0” and “+1” have been
  previously set (see the command ``builtin`` in :doc:`commands`)

**Remark:** for any regular identifier ``i``, ``{|i|}`` is equivalent
to ``i``.

**Remark:** escaped identifiers and regular identifiers ending with a
non-negative integer with leading zeros cannot be used for bound
variable names.

**Convention:** identifiers starting with an uppercase letter denote
types and predicates (e.g.  ``Nat``, ``List``), and identifiers
starting with a lowercase letter denote constructors, functions and proofs
(e.g. ``zero``, ``add``, ``refl``).

Terms
-----
A user-defined term can be either:

* ``TYPE``, the sort for types

* a possibly qualified identifier denoting either:

   * a qualified symbol or a non-qualified symbol previously declared in the
     current file or in some previously open module, possibly prefixed by ``@``
     to disallow implicit arguments
   * a bound variable
   * a metavariable or goal when prefixed by ``?``

* an anonymous function ``λ(x:A) y z,t`` mapping ``x``, ``y`` and ``z``
  (of type ``A`` for ``x``) to ``t``

* a dependent product ``Π(x:A) y z,T``

* a non-dependent product ``A → T`` (syntactic sugar for ``Π x:A,T`` when ``x``
  does not occur in ``T``)

* a ``let f (x:A) y z: T ≔ t in`` construction

* an application written by space-separated juxtaposition, except for
  symbol identifiers declared as infix (e.g. ``x + y``)

* a meta-variable application ``?M.[t;u;v]``. ``?M`` alone, without arguments
  between square brackets, is a shorthand for ``?M.[x1;..;xn]`` where
  ``x1;..;xn`` are all the variables of the context.

* a pattern-variable application ``$P.[x;y]`` (in rules only). ``$P``
  alone, without arguments between square brackets, is a shorthand for
  ``$P.[]``. This short-hand is not allowed under binders.

* ``_`` for an unknown term or a term we don't care about. It is replaced by a
  fresh metavariable (or a fresh pattern variable in a rule left-hand side)
  applied to all the variables of the context.

* an integer between 0 and 2^30-1 if the :ref:`builtins <builtin>` "0" and "+1" are defined

* a term enclosed between square brackets ``[`` … ``]`` for explicitly
  giving the value of an argument declared as implicit
  
Subterms can be parenthesized to avoid ambiguities.
