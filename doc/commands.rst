Commands
========

The BNF grammar of Lambdapi is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

Lambdapi files are formed of a list of commands. A command starts with
a particular reserved keyword and ends with a semi-colon.

One-line comments are introduced by ``//``:

::

   // These words are ignored

Multi-line comments are opened with ``/*`` and closed with ``*/``. They can be nested.

::

   /* These
      words are
      ignored /* these ones too */ */

.. _builtin:

``builtin``
---------------

The command ``builtin`` allows to map an internally defined string
literal ``"…"`` to a user symbol identifier. Those mappings are
necessary for other commands, tactics or notations to work.

.. _coerce_rule:

``coerce_rule``
---------------

Lambdapi can be instructed to insert function applications into terms whenever
needed for typability. These functions are called *coercions*. For instance,
assuming we have a type ``Float``, a type ``Int`` and a function
``FloatOfInt : Int → Float``, the latter function can be declared
as a coercion from integers to floats with the declaration

::

    coerce_rule coerce Int Float $x ↪ FloatOfInt $x;

Symbol ``coerce`` is a built-in function symbol that computes the coercion.
Whenever a term ``t`` of type ``Int`` is found when Lambadpi expected a
``Float``, ``t`` will be replaced by ``coerce Int Float t`` and reduced.
The declared coercion will allow the latter term to be reduced to
``FloatOfInt t``.

Coercions can call the function ``coerce`` recursively,
which allows to write, e.g.

::

    coerce_rule coerce (List $a) (List $b) $l ↪ map (λ e: El $a, coerce $a $b e) $l;

where ``Set: TYPE;``, ``List : Set → TYPE``, ``El : Set → TYPE`` and ``map`` is
the usual map operator on lists such that ``map f (cons x l) ≡ cons (f x) (map l)``.

*WARNING* Coercions are still experimental and may not mix well with
metavariables. Indeed, the term ``coerce ?1 Float t`` will not reduce to
``FloatOfInt t`` even if the equation ``?1 ≡ Int`` has been registered during
typing. Furthermore, for the moment, it is unsafe to have symbols that can be
reduced to protected symbols in the right-hand side of coercions:
reduction may occur during coercion elaboration,
which may generate unsound protected symbols.

.. _inductive:

``inductive``
-------------

The commands ``symbol`` and ``rules`` above are enough to define
inductive types, their constructors, their induction
principles/recursors and their defining rules.

We however provide a command ``inductive`` for automatically
generating the induction principles and their rules from an inductive
type definition, assuming that the following builtins are defined:

::

   ￼builtin "Prop" ≔ ...; // : TYPE, for the type of propositions
   ￼builtin "P"    ≔ ...; // : Prop → TYPE, interpretation of propositions as types

An inductive type can have 0 or more constructors.

The name of the induction principle is ``ind_`` followed by the name
of the type.

The command currently supports parametrized mutually defined dependent
strictly-positive data types only. As usual, polymorphic types can be
encoded by defining a type ``Set`` and a function ``τ:Set → TYPE``.

Example:

::

   ￼inductive ℕ : TYPE ≔
   ￼| zero: ℕ
   ￼| succ: ℕ → ℕ;

is equivalent to:

::

   ￼constant symbol ℕ : TYPE;
   ￼constant symbol zero : ℕ;
   ￼constant symbol succ : ℕ → ℕ;
   ￼symbol ind_ℕ p : π(p zero) → (Π x, π(p x) → π(p(succ x))) → Π x, π(p x);
   ￼rule ind_ℕ _ $pz _ zero ↪ $pz
   ￼with ind_ℕ $p $pz $ps (succ $n) ↪ $ps $n (ind_ℕ $p $pz $ps $n);

For mutually defined inductive types, one needs to use the ``with``
keyword to link all inductive types together.

Inductive definitions can also be parametrized as follows:

::

   (a:Set) inductive T: TYPE ≔
   | node: τ a → F a → T a
   with F: TYPE ≔
   | nilF: F a
   | consF: T a → F a → F a;

Note that parameters are set as implicit in the types of
constructors. So, one has to write ``consF t l`` or ``@consF a t l``.

For mutually defined inductive types, an induction principle is
generated for each inductive type:

::

   assert ⊢ ind_F: Π a, Π p:T a → Prop, Π q:F a → Prop,
     (Π x l, π(q l) → π(p (node x l))) →
     π(q nilF) →
     (Π t, π(p t) → Π l, π(q l) → π(q (consF t l))) →
     Π l, π(q l);
   assert ⊢ ind_T: Π a, Π p:T a → Prop, Π q:F a → Prop,
     (Π x, Π l, π(q l) → π(p (node x l))) →
     π(q nilF) →
     (Π t, π(p t) → Π l, π(q l) → π(q (consF t l))) →
     Π t, π(p t);

Finaly, here is an example of strictly-positive inductive type:

::

   inductive 𝕆:TYPE ≔ z:𝕆 | s:𝕆 → 𝕆 | l:(ℕ → 𝕆) → 𝕆;

   assert ⊢ ind_𝕆: Π p, π (p z) → (Π x, π (p x) → π (p (s x)))
     → (Π x, (Π y, π (p (x y))) → π (p (l x))) → Π x, π (p x);

   assert p a b c ⊢ ind_𝕆 p a b c z ≡ a;
   assert p a b c x ⊢ ind_𝕆 p a b c (s x) ≡ b x (ind_𝕆 p a b c x);
   assert p a b c x y ⊢ ind_𝕆 p a b c (l x) ≡ c x (λ y, ind_𝕆 p a b c (x y));

.. _notation:

``notation``
----------------

The ``notation`` commands associate to a symbol identifier (declared
in the current module or in another module) a specific notation used
by the parser and the printer of the system. The possible notations
are:

- **infix**

  ::

    notation + infix left 6.5;
    notation * infix left 7;


  * With the above notation, the system now expects ``+`` to only
    appear in expressions of the form ``x + y``. As a consequence,
    ``+`` is not a valid term anymore. To locally deactivate a
    notation, you can use ``(+)`` or ``@+`` instead.

  * A symbol declared as infix must have a type of the form ``A → A →
    A``.

  * The additional keyword ``left`` declares the symbol associative to
    the left, that is, ``x + y + z`` is parsed as ``(x + y) +
    z``. Symmetrically, the additional keyword ``right`` declares the
    symbol associative to the right, that is, ``x + y + z`` is parsed
    as ``x + (y + z)``.

  * Priority levels are used to disambiguate expressions mixing
    several operators. Hence, with the priorities declared above,
    ``x + y * z`` is parsed as ``x + (y * z)``.

  * Priorities can be natural numbers or floating point
    numbers. Hence, a priority can (almost) always be inserted between
    two different levels.

- **prefix/postfix**

  ::

   notation ¬ prefix 5;
   notation ! postfix 10;

  * Infix, prefix and postfix operators share the same levels of
    priority. Hence, depending on the priorities, ``-x + z`` is
    parsed as ``(-x) + z`` or as ``-(x + z)``.

  * Non-operator application (such as ``f x`` where ``f`` and ``x``
    are not operators) has a higher priority than any operator
    application. Hence, if ``-`` is declared as prefix, then ``- f x``
    is always parsed ``- (f x)``, no matter the priority of ``-`` is.

  * The functional arrow has a lower priority than any operator.
    Hence, ``- A → A`` is always parsed ``(- A) → A``, whatever the
    priority of ``-`` is.

- **quantifier** allows to write ```f x, t`` instead of ``f (λ x, t)``:

  ::

   symbol ∀ {a} : (T a → Prop) → Prop;
   notation ∀ quantifier;
   compute λ p, ∀ (λ x:T a, p); // prints `∀ x, p
   type λ p, `∀ x, p; // quantifiers can be written as such
   type λ p, `f x, p; // works as well if f is any symbol

.. _opaque:

``opaque``
---------------

The command ``opaque`` allows to set opaque (see **Opacity modifier**) a previously defined symbol.

::

   symbol πᶜ p ≔ π (¬ ¬ p); // interpretation of classical propositions as types
   opaque πᶜ;

.. _open:

``[private] open``
------------------

Puts into scope the symbols of the previously required modules given
in arguments. It can also be combined with the ``require`` command.

Non-private ``open`` commands are transitively inherited: if A opens B
and B opens C, then the symbols of C are also put in scope in the
environment of A.

::

   require std.bool;
   open std.bool;
   require open church.sums;

Note that ``open`` always takes as arguments qualified
identifiers. See :doc:`module` for more details.

Note that aliased modules cannot be open.

.. _require:

``require``
-----------

Informs Lambdapi to import in the current environment the (non
private) symbols, rules and builtins declared or defined in some other
modules. These symbols can be used by prefixing them with their module
path: if a module ``Stdlib.Bool`` declares a symbol ``true`` then,
after ``require Stdlib.Bool``, one can use ``true`` by writing
``Stdlib.Bool.true``. It is possible to get rid of the prefix by using
the ``open`` command.

Dependencies are transitively inherited: if A requires B and B
requires C, then the symbols of C are also imported in the current
environment.

A required module also can be aliased.

::

   require std.bool;
   require church.list as list;

Note that ``require`` always takes as arguments qualified
identifiers. See :doc:`module` for more details.

.. _rule:

``rule``
--------

Rewriting rules for definable symbols are declared using the ``rule``
command.

::

   rule add zero      $n ↪ $n;
   rule add (succ $n) $m ↪ succ (add $n $m);
   rule mul zero      _  ↪ zero;

Identifiers prefixed by ``$`` are pattern variables.

User-defined rules are assumed to form a confluent (the order of rule
applications is not important) and terminating (there is no infinite
rewrite sequences) rewriting system when combined with β-reduction.

The verification is left to the user, who can call external provers
for trying to check those properties automatically using the
:doc:`command line options <options>` ``--confluence`` and
``--termination``.

Lambdapi will however try to check at each ``rule`` command that the
added rules preserve local confluence, by checking the joinability of
critical pairs between the added rules and the rules already added in
the signature (critical pairs involving AC symbols or non-nullary
pattern variables are currently not checked). A warning is output if
Lambdapi finds a non-joinable critical pair. To avoid such a warning,
it may be useful to declare several rules in the same ``rule`` command
by using the keyword ``with``:

::

   rule add zero      $n ↪ $n
   with add (succ $n) $m ↪ succ (add $n $m);

Rules must also preserve typing (subject-reduction property), that is,
if an instance of a left-hand side has some type, then the
corresponding instance of the right-hand side should have the same
type. Lambdapi implements an algorithm trying to check this property
automatically, and will not accept a rule if it does not pass this
test.

**Higher-order pattern-matching**. Lambdapi allows higher-order
pattern-matching on patterns à la Miller but modulo β-equivalence only
(and not βη).

::

   rule diff (λx, sin $F.[x]) ↪ λx, diff (λx, $F.[x]) x × cos $F.[x];

Patterns can contain abstractions ``λx, _`` and the user may attach an
environment made of *distinct* bound variables to a pattern variable
to indicate which bound variable can occur in the matched term. The
environment is a semicolon-separated list of variables enclosed in
square brackets preceded by a dot: ``.[x;y;...]``. For instance, a
term of the form ``λx y,t`` matches the pattern ``λx y,$F.[x]`` only
if ``y`` does not freely occur in ``t``.

::

   rule lam (λx, app $F.[] x) ↪ $F; // η-reduction

Hence, the rule ``lam (λx, app $F.[] x) ↪ $F`` implements η-reduction
since no valid instance of ``$F`` can contain ``x``.

Pattern variables cannot appear at the head of an application:
``$F.[] x`` is not allowed. The converse ``x $F.[]`` is allowed.

A pattern variable ``$P.[]`` can be shortened to ``$P`` when there is no
ambiguity, i.e. when the variable is not under a binder (unlike in the
rule η above).

It is possible to define an unnamed pattern variable with the syntax
``$_.[x,y]``.

The unnamed pattern variable ``_`` is always the most general: if ``x``
and ``y`` are the only variables in scope, then ``_`` is equivalent to
``$_.[x,y]``.

In rule left-hand sides, λ-expressions cannot have type annotations.

**Important**. In contrast to languages like OCaml, Coq, Agda, etc. rule
left-hand sides can contain defined symbols:

::

   rule add (add x y) z ↪ add x (add y z);

They can overlap:

::

   rule add zero x ↪ x
   with add x zero ↪ x;

And they can be non-linear:

::

   rule minus x x ↪ zero;

Other examples of patterns are available in `patterns.lp <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/patterns.lp>`__.

.. _symbol:

``symbol``
----------

Allows to declare or define a symbol as follows:

*modifiers* ``symbol`` *identifier* *parameters* [``:`` *type*] [``≔`` *term*] [``begin`` *proof* ``end``] ``;``

The identifier should not have already been used in the current module.
It must be followed by a type or a definition (or both).

The following proof (if any) allows the user to solve typing and
unification goals the system could not solve automatically. It can
also be used to give a definition interactively (if no defining term
is provided).

Without ``≔``, this is just a symbol declaration. Note that, in this
case, the following proof script does *not* provide a proof of *type*
but help the system solve unification constraints it couldn't solve
automatically for checking the well-sortedness of *type*.

For defining a symbol or proving a theorem, which is the same thing,
``≔`` is mandatory. If no defining *term* is provided, then the
following proof script must indeed include a proof of *type*. Note
that ``symbol f:A ≔ t`` is equivalent to ``symbol f:A ≔ begin refine t
end``.

Examples:

::

   symbol N:TYPE;

   // with no proof script
   symbol add : N → N → N; // a type but no definition (axiom)
   symbol double n ≔ add n n; // no type but a definition
   symbol triple n : N ≔ add n (double n); // a type and a definition

   // with a proof script (theorem or interactive definition)
   symbol F : N → TYPE;
   symbol idF n : F n → F n ≔
   begin
     assume n x; apply x;
   end;

**Modifiers:**

Modifiers are keywords that precede a symbol declaration to provide
the system with additional information on its properties and behavior.

- **Opacity modifier**:

  - ``opaque``: The symbol will never be reduced to its
    definition. This modifier is generally used for actual theorems.

- **Property modifiers** (used by the unification engine or the conversion):

  - ``constant``: No rule or definition can be given to the symbol
  - ``injective``: The symbol can be considered as injective, that is, if ``f t1 .. tn`` ≡ ``f u1 .. un``, then ``t1``\ ≡\ ``u1``, …, ``tn``\ ≡\ ``un``. For the moment, the verification is left to the user.
  - ``commutative``: Adds in the conversion the equation ``f t u ≡ f u t``.
  - ``associative``: Adds in the conversion the equation ``f (f t u) v ≡ f t (f u v)`` (in conjonction with ``commutative`` only).

    For handling commutative and associative-commutative symbols,
    terms are systemically put in some canonical form following a
    technique described `here
    <http://dx.doi.org/10.1007/978-3-540-71316-6_8>`__.

    If a symbol ``f`` is ``commutative`` and not ``associative`` then,
    for every canonical term of the form ``f t u``, we have ``t ≤ u``,
    where ``≤`` is a total ordering on terms left unspecified.

    If a symbol ``f`` is ``commutative`` and ``associative left`` then
    there is no canonical term of the form ``f t (f u v)`` and thus
    every canonical term headed by ``f`` is of the form ``f … (f (f t₁
    t₂) t₃) …  tₙ``. If a symbol ``f`` is ``commutative`` and
    ``associative`` or ``associative right`` then there is no
    canonical term of the form ``f (f t u) v`` and thus every
    canonical term headed by ``f`` is of the form ``f t₁ (f t₂ (f t₃ …
    tₙ) … )``. Moreover, in both cases, we have ``t₁ ≤ t₂ ≤ … ≤ tₙ``.

- **Exposition modifiers** define how a symbol can be used outside the
  module where it is defined. By default, the symbol can be used
  without restriction.

  - ``private``: The symbol cannot be used.
  - ``protected``: The symbol can only be used in left-hand side of
    rewrite rules.

  Exposition modifiers obey the following rules: inside a module,

  - Private symbols cannot appear in the type of public symbols.
  - Private symbols cannot appear in the right-hand side of a
    rewriting rule defining a public symbol.
  - Externally defined protected symbols cannot appear at the head of
    a left-hand side.
  - Externally defined protected symbols cannot appear in the right
    hand side of a rewriting rule.

- **Matching strategy modifier:**

  - ``sequential``: modifies the pattern matching algorithm. By default,
    the order of rule declarations is not taken into account. This
    modifier tells Lambdapi to apply rules defining a sequential symbol
    in the order they have been declared (note that the order of the
    rules may depend on the order of the ``require`` commands). An
    example can be seen in ``tests/OK/rule_order.lp``.
    *WARNING:* using this modifier can break important properties.

Examples:

::

   constant symbol Nat : TYPE;
   constant symbol zero : Nat;
   constant symbol succ (x:Nat) : Nat;
   symbol add : Nat → Nat → Nat;
   opaque symbol add0 n : add n 0 = n ≔ begin ... end; // theorem
   injective symbol double n ≔ add n n;
   constant symbol list : Nat → TYPE;
   constant symbol nil : List zero;
   constant symbol cons : Nat → Π n, List n → List(succ n);
   private symbol aux : Π n, List n → Nat;

**Implicit arguments:** Some arguments can be declared as implicit by
encloding them into square brackets ``[`` … ``]``. Then, they must not
be given by the user later.  Implicit arguments are replaced by ``_``
at parsing time, generating fresh metavariables. An argument declared
as implicit can be explicitly given by enclosing it between square
brackets ``[`` … ``]`` though. If a function symbol is prefixed by
``@`` then the implicit arguments mechanism is disabled and all the
arguments must be explicitly given.

::

   symbol eq [a:U] : T a → T a → Prop;
   // The first argument of "eq" is declared as implicit and must not be given
   // unless "eq" is prefixed by "@".
   // Hence, "eq t u", "eq [_] t u" and "@eq _ t u" are all valid and equivalent.

**Notations**: Some notation can be declared for a symbol using the
commands :ref:`notation` and :ref:`builtin`.

.. _unif_rule:

``unif_rule``
-----------------

The unification engine can be guided using
*unification rules*. Given a unification problem ``t ≡ u``, if the
engine cannot find a solution, it will try to match the pattern
``t ≡ u`` against the defined rules (modulo commutativity of ≡)
and rewrite the problem to the
right-hand side of the matched rule. Variables of the RHS that do
not appear in the LHS are replaced by fresh metavariables on rule application.

Examples:

::

   unif_rule Bool ≡ T $t ↪ [ $t ≡ bool ];
   unif_rule $x + $y ≡ 0 ↪ [ $x ≡ 0, $y ≡ 0 ];
   unif_rule $a → $b ≡ T $c ↪ [ $a ≡ T $a', $b ≡ T $b', $c ≡ arrow $a' $b' ];

Thanks to the first unification rule, a problem ``T ?x ≡ Bool`` is
transformed into ``?x ≡ bool``.

*WARNING* This feature is experimental and there is no sanity check
performed on the rules.
