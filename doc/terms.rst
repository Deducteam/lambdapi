Syntax of terms
===============

The BNF grammar of Lambdapi is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

Identifiers
-----------
An identifier can be:

* a *regular* identifier: ``/`` or an arbitrary non-empty sequence of
  UTF-8 codepoints not among ``\t\r\n :,;`(){}[]".@$|?/`` that is not
  an integer number

* an *escaped* identifier: an arbitrary sequence of characters
  enclosed between ``{|`` and ``|}``

**Remark:** for any regular identifier ``i``, ``{|i|}`` and ``i`` are
identified.

**Convention:** identifiers starting with an uppercase letter denote
types (e.g.  ``Nat``, ``List``), and identifiers starting with a
lowercase letter denote constructors, functions and proofs
(e.g. ``zero``, ``add``, ``refl``).

Qualified identifiers
---------------------
A qualified identifier is an identifier of the form
``dir1.`` … ``dirn.file.id`` denoting the function symbol ``id`` defined
in the file ``dir1/`` … ``/dirn/file.lp``. To be used, ``dir1.`` …
``dirn.file`` must be required first.

**Remark**: ``dir1``, …, ``dirn`` cannot be natural numbers.

Terms
-----
A user-defined term can be either:

* ``TYPE``, the sort for types

* an unqualified identifier denoting a bound variable

* a qualified or a non-qualified symbol previously declared in the
  current file or in some previously open module, possibly prefixed by
  ``@`` to disallow implicit arguments

* an anonymous function ``λ (x:A) y z,t`` mapping ``x``, ``y`` and ``z``
  (of type ``A`` for ``x``) to ``t``

* a dependent product ``Π (x:A) y z,T``

* a non-dependent product ``A → T`` (syntactic sugar for ``Π x:A,T`` when ``x``
  does not occur in ``T``)

* a ``let f (x:A) y z : T ≔ t in u`` construction

* an application written by space-separated juxtaposition, except for
  symbols having an infix :ref:`notation` (e.g. ``x + y``)

* an infix symbol application ``x + y``

* an identifier wrapped in parentheses to access its notationless
  value (e.g. ``(+)``)

* a metavariable application ``?0.[x;y]`` that has been generated
  previously. ``?0`` alone can be used as a short-hand for ``?0.[]``.

* a pattern-variable application ``$P.[x;y]`` (in rules only). ``$P``
  alone can be used as a shorthand for ``$P.[]``, except under binders
  (to avoid mistakes).

* ``_`` for an unknown term or a term we don't care about.  It will be
  replaced by a fresh metavariable in terms, or a fresh pattern
  variable in a rule left-hand side, applied to all the variables of
  the context.

* a term enclosed between square brackets ``[`` … ``]`` for explicitly
  giving the value of an argument declared as implicit

.. String-builtin:

* a string enclosed between double quotes if the following :ref:`builtin <builtin>` is defined:

::

   builtin "String" := …; // : TYPE

* a (signed) integer if the following builtins are defined:

::

   builtin "0"  ≔ …; // : T
   builtin "1"  ≔ …; // : T
   …
   builtin "10" := …; // : T
   builtin "+" := …; // : T → T → T
   builtin "*" := …; // : T → T → T
   builtin "-" := …; // : T → T // (optional)
   type 42;

Subterms can be parenthesized to avoid ambiguities.

Decimal notation
----------------
The system can also print the values of various types using a decimal notation by defining the following builtins:

* Natural numbers in base 1 (Peano numbers):

::
   
   builtin "nat_zero" ≔ ...; // : N
   builtin "nat_succ" ≔ ...; // : N → N

* Positive natural numbers in base 2:

::
   
   builtin "pos_one" ≔ ...; // : P
   builtin "pos_double" ≔ ...; // : P → P
   builtin "pos_succ_double" ≔ ...; // : P → P

* Integer numbers in base 2:

::
   
   builtin "int_zero" ≔ ...; // : Z
   builtin "int_positive" ≔ ...; // : P → Z
   builtin "int_negative" ≔ ...; // : P → Z
