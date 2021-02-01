Commands
========

The BNF grammar of Lambdapi is in `syntax.bnf <syntax.bnf>`__.

In this section, we will illustrate the syntax of Lambdapi using
examples. The first thing to note is that Lambdapi files are formed of a
list of commands. A command starts with a particular reserved keyword
and ends with a semi-colon.

One-line comments are introduced by ‘//’:

::

   // all this is ignored

And multi-line comments are opened with ‘/*’ and closed with ‘*/’.

::

   /* These
      words are
      ignored */

``require``
-----------

Informs the type-checker that the current module
depends on some other module, which must hence be compiled.

::

   require boolean;
   require church.list as list;

Note that a required module can optionally be aliased, in which case it
can be referred to with the provided name.

``open``
--------

Puts into scope the symbols defined in the given
module. It can also be combined with the ``require`` command.

::

   open booleans;
   require open church.sums;

``symbol``
----------

Allows to declare or define a symbol as follows:

``symbol`` *modifiers* *identifier* *parameters* [``:`` *type*] [``≔`` *term*] [``begin`` *proof* ``end``] ``;``

The identifier should not have already been used in the current module.
It must be followed by a type or a definition (or both).

The following proof (if any) allows the user to solve typing and
unification goals the system could not solve automatically. It can
also be used to give a definition interactively (if no defining term
is provided).

Without ``≔``, this is just a symbol declaration. The following proof
script does *not* provide a proof of *type* but help the system solve
unification constraints it couldn't solve automatically for checking
the well-sortedness of *type*.

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
     assume n x;
     apply x;
   end;

**Modifiers:**

Modifiers are keywords that precede a symbol declaration to provide
the system with additional information on its properties or behavior.

- Modifiers for the unification engine:

  - ``constant``: no rule can be added to the symbol
  - ``injective``: the symbol can be considered as injective, that is, if ``f t1 .. tn`` ≡ ``f u1 .. un``, then ``t1``\ ≡\ ``u1``, …, ``tn``\ ≡\ ``un``. For the moment, the verification is left to the user.

-  Exposition markers define how a symbol can be used outside the module
   where it is defined.

   -  by default, the symbol can be used without restriction
   -  ``private``: the symbol cannot be used
   -  ``protected``: the symbol can only be used in left-hand side of
      rewrite rules.

   Exposition markers obey the following rules: inside a module,

   -  private symbols cannot appear in the type of public symbols;
   -  private symbols cannot appear in the right-hand side of a
      rewriting rule defining a public symbol
   -  externally defined protected symbols cannot appear at the head of
      a left-hand side
   -  externally defined protected symbols cannot appear in the right
      hand side of a rewriting rule

-  ``sequential``: modifies the pattern matching algorithm. By default,
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
encloding them into curly brackets ``{`` … ``}``. Then, they must not
be given by the user later.  Implicit arguments are replaced by ``_``
at parsing time, generating fresh metavariables. An argument declared
as implicit can be explicitly given by enclosing it between curly
brackets ``{`` … ``}`` though. If a function symbol is prefixed by
``@`` then the implicit arguments mechanism is disabled and all the
arguments must be explicitly given.

::

   symbol eq {a:U} : T a → T a → Prop;
   // The first argument of `eq` is declared as implicit and must not be given
   // unless `eq` is prefixed by `@`.
   // Hence, [eq t u], [eq {_} t u] and [@eq _ t u] are all valid and equivalent.

**Notations**: Some notation can be declared for some symbol. See the command
``set``.

``rule``
--------

Rewriting rules for definable symbols are declared using the ``rule``
command.

::

   rule add zero      $n ↪ $n;
   rule add (succ $n) $m ↪ succ (add $n $m);
   rule mul zero      _  ↪ zero;

Terms prefixed by the sigil ``$`` and ``_`` are pattern variables.

**Higher-order pattern-matching**. Lambdapi allows higher-order
pattern-matching on patterns à la Miller but modulo β-equivalence only
(and not βη).

::

   rule diff (λx, sin $F[x]) ↪ λx, diff (λx, $F[x]) x × cos $F[x];

Patterns can contain abstractions ``λx, _`` and the user may attach an
environment made of *distinct* bound variables to a pattern variable to
indicate which bound variable can occur in the matched term. The
environment is a semicolon-separated list of variables enclosed in
square brackets ``[x;y;...]``. For instance, a term of the form
``λx y,t`` matches the pattern ``λx y,$F[x]`` only if ``y`` does not
freely occur in ``t``.

::

   rule lam (λx, app $F[] x) ↪ $F; // η-reduction

Hence, the rule ``lam (λx, app $F[] x) ↪ $F`` implements η-reduction
since no valid instance of ``$F`` can contain ``x``.

Pattern variables cannot appear at the head of an application:
``$F[] x`` is not allowed. The converse ``x $F[]`` is.

A pattern variable ``$P[]`` can be shortened to ``$P`` when there is no
ambiguity, i.e. when the variable is not under a binder (unlike in the
rule η above).

It is possible to define an unnamed pattern variable with the syntax
``$_[x;y]``.

The unnamed pattern variable ``_`` is always the most general: if ``x``
and ``y`` are the only variables in scope, then ``_`` is equivalent to
``$_[x;y]``.

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

Note that rewriting rules can also be defined simultaneously, using the
``with`` keyword instead of the ``rule`` keyword for all but the first
rule.

::

   rule add zero      $n ↪ $n
   with add (succ $n) $m ↪ succ (add $n $m);

Adding sets of rules allows to maintain confluence.

Examples of patterns are available in ``tests/OK/patterns.lp``.

``set prefix|infix|quantifier|builtin|unif_rule``
----------------------------------------------------------

The ``set`` command is used to control the behaviour of Lambdapi and
extension points in its syntax.

**prefix symbols** The following code defines a prefix symbol for
negation.

::

   set prefix 5 "¬" ≔ neg;

**infix symbols** The following code defines infix symbols for addition
and multiplication. Both are associative to the left, and they have
priority levels ``6`` and ``7`` respectively.

::

   set infix left 6 "+" ≔ add;
   set infix left 7 "×" ≔ mul;

The modifier ``infix``, ``infix right`` and ``infix left`` can be used
to specify whether the defined symbol is non-associative, associative to
the right, or associative to the left. The priority levels are floating
point numbers, hence a priority can (almost) always be inserted between
two different levels.

**quantifier symbols** Any symbol can be input as a quantifier (as done usually
with symbols such as ``∀``, ``∃`` or ``λ``), provided that it
is prefixed with a backquote `` \` ``. However, such terms will be printed as
quantifiers only if they are declared so using the command ``set quantifier``:

::

   set quantifier ∀; // : Π {a}, (T a → Prop) → Prop
   compute ∀ {a'} (λx:T a,p); // prints `∀x:T a,p
   compute ∀ (λx:T a, p); // prints `∀x,p
   type `∀ x, p; // quantifiers can be written as such
   type `f x, p; // works as well if f is defined

**builtins** The command ``set builtin`` allows to map a “builtin“
string to a user-defined symbol identifier. Those mappings are
necessary for other commands or tactics. For instance, to use decimal
numbers, one needs to map the builtins “0“ and “+1“ to some symbol
identifiers for zero and the successor function (see hereafter); to
use tactics on equality, one needs to define some specific builtins;
etc.

**notation for natural numbers** It is possible to use the standard
decimal notation for natural numbers by specifying the symbols
representing 0 and the successor function as follows:

::

   set builtin "0"  ≔ zero; // : N
   set builtin "+1" ≔ succ; // : N → N

**unification rules** The unification engine can be guided using
*unification rules*. Given a unification problem ``t ≡ u``, if the
engine cannot find a solution, it will try to match the pattern
``t ≡ u`` against the defined rules (modulo commutativity of ≡)
and rewrite the problem to the
right-hand side of the matched rule. Variables of the RHS that do
not appear in the LHS are replaced by fresh metavariables on rule application.

Examples:

::

   set unif_rule Bool ≡ T $t ↪ begin $t ≡ bool end;
   set unif_rule $x + $y ≡ 0 ↪ begin $x ≡ 0; $y ≡ 0 end;
   set unif_rule $a → $b ≡ T $c ↪ begin $a ≡ T $a'; $b ≡ T $b'; $c ≡ arrow $a' $b' end;

Thanks to the first unification rule, a problem ``T ?x ≡ Bool`` is
transformed into ``?x ≡ bool``.

*WARNING* This feature is experimental and there is no sanity check
performed on the rules.

``inductive``
-------------

The commands ``symbol`` and ``rules`` above are enough to define
inductive types, their constructors, their induction
principles/recursors and their defining rules.

We however provide a command ``inductive`` for automatically
generating the induction principles and their rules from an inductive
type definition, assuming that the following builtins are defined:

::
   
   ￼set builtin "Prop" ≔ ...; // : TYPE, for the type of propositions
   ￼set builtin "P"    ≔ ...; // : Prop → TYPE, interpretation of propositions as types

Currently, it only supports parametrized mutually defined dependent
first-order data types. As usual, polymorphic types can be encoded by
defining a type ``Set`` and a function ``τ:Set → TYPE``.

The name of the induction principle is ``ind_`` followed by the name
of the type.

Example:

::
   
   ￼inductive ℕ : TYPE ≔
   ￼ | zero: ℕ
   ￼ | succ: ℕ → ℕ;
   
is equivalent to:
￼
::
   
   ￼injective symbol ℕ : TYPE;
   ￼constant  symbol zero : ℕ;
   ￼constant  symbol succ : ℕ → ℕ;
   ￼symbol ind_ℕ p :
      π(p zero) → (Π x, π(p x) → π(p(succ x))) → Π x, π(p x);
   ￼rule ind_ℕ _ $pz _ zero ↪ $pz
   ￼with ind_ℕ $p $pz $ps (succ $n) ↪ $ps $n (ind_ℕ $p $pz $ps $n);


For mutually defined inductive types, one needs to use the ``with``
keyword to link all inductive types together:

::
   
   (a:Set)
   inductive T: TYPE ≔
   | node: τ a → F a → T a
   with F: TYPE ≔
   | nilF: F a
   | consF: T a → F a → F a;

In case of a parametrized definition like the previous one, parameters
are set as implicit in the types of constructors. So, one has to write
``consF t l`` or ``@consF a t l``.
