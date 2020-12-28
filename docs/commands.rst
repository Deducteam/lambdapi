Commands
========

The BNF grammar of Lambdapi is in `syntax.bnf <syntax.bnf>`__.

In this section, we will illustrate the syntax of Lambdapi using
examples. The first thing to note is that Lambdapi files are formed of a
list of commands. A command starts with a particular reserved keyword
and ends either at the start of a new command or at the end of the
file.

One-line comments are introduced by ‘//’:

::

   // all this is ignored

In Emacs, one can (un)comment a region by using Meta-; .

``require``
-----------

Informs the type-checker that the current module
depends on some other module, which must hence be compiled.

::

   require boolean
   require church.list as list

Note that a required module can optionally be aliased, in which case it
can be referred to with the provided name.

``open``
--------

Puts into scope the symbols defined in the given
module. It can also be combined with the ``require`` command.

::

   open booleans
   require open church.sums

``symbol``
----------

Allows to declare or define a symbol as follows:

``symbol`` *modifiers* *identifier* *parameters* [``:`` *type*] [``≔`` *term*] [``begin`` *proof* ``end``]

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

   symbol N:TYPE

   // with no proof script
   symbol add : N → N → N // a type but no definition (axiom)
   symbol double n ≔ add n n // no type but a definition
   symbol triple n : N ≔ add n (double n) // a type and a definition

   // with a proof script (theorem or interactive definition)
   symbol F : N → TYPE
   symbol idF n : F n → F n ≔
   begin
     solve
     assume n x
     apply x
   end

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

   constant symbol Nat : TYPE
   constant symbol zero : Nat
   constant symbol succ (x:Nat) : Nat
   symbol add : Nat → Nat → Nat
   opaque symbol add0 n : add n 0 = n ≔ begin ... end // theorem
   injective symbol double n ≔ add n n
   constant symbol list : Nat → TYPE
   constant symbol nil : List zero
   constant symbol cons : Nat → Πn, List n → List(succ n)
   private symbol aux : Πn, List n → Nat

**Implicit arguments:** Some arguments can be declared as implicit by
encloding them into curly brackets ``{`` … ``}``. Then, they must not
be given by the user later.  Implicit arguments are replaced by ``_``
at parsing time, generating fresh metavariables. An argument declared
as implicit can be explicitly given by enclosing it between curly
brackets ``{`` … ``}`` though. If a function symbol is prefixed by
``@`` then the implicit arguments mechanism is disabled and all the
arguments must be explicitly given.

::

   symbol eq {a:U} : T a → T a → Prop
   // The first argument of `eq` is declared as implicit and must not be given
   // unless `eq` is prefixed by `@`.
   // Hence, [eq t u], [eq {_} t u] and [@eq _ t u] are all valid and equivalent.

**Notations**: Some notation can be declared for some symbol. See the command
``set``.

``inductive``
-------------
The command ``inductive`` can be used to define an inductive type, its constructors and its associated induction principle if it can be generated. The name of the induction principle is the name of the type prefixed with ``ind_``. For generating the induction principle, we assume defined the following builtins:

::
   
   ￼set builtin "Prop" ≔ ... // : TYPE
   ￼set builtin "P"    ≔ ... // : Prop → TYPE

For the moment, we only support (mutually defined) first-order dependent types.
Polymorphic types can be encoded by defining a type Set and a function τ:Set→TYPE.

Some cases of nested type are supported too, like the type Bush.
Example:

::
   
   ￼inductive Nat : TYPE ≔
   ￼ | z    : Nat
   ￼ | succ : Nat → Nat
   
is equivalent to:
￼
::
   
   ￼injective symbol Nat  : TYPE
   ￼constant  symbol z    : Nat
   ￼constant  symbol succ : Nat → Nat
   ￼symbol ind_Nat p : π (p 0) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)
   ￼rule ind_Nat _  $pz    _       z     ↪ $pz
   ￼with ind_Nat $p $pz $psucc (succ $n) ↪ $psucc $n (ind_Nat $p $pz $psucc $n)

Note that to define mutually defined inductive types, you need the ``with`` keyword to link
all inductive types together. For instance:

::
   
   ￼inductive Expr : TYPE ≔
      | Lit : Nat → Expr
      | Add : Expr → Expr → Expr
      | If  : BExpr → Expr → Expr → Expr
    with BExpr : TYPE ≔
      | BLit  : Bool → BExpr
      | And   : BExpr → BExpr → BExpr
      | Not   : BExpr → BExpr
      | Equal : Expr → Expr → BExpr

``rule``
--------

Rewriting rules for definable symbols are declared using the ``rule``
command.

::

   rule add zero      $n ↪ $n
   rule add (succ $n) $m ↪ succ (add $n $m)
   rule mul zero      _  ↪ zero

Terms prefixed by the sigil ``$`` and ``_`` are pattern variables.

**Higher-order pattern-matching**. Lambdapi allows higher-order
pattern-matching on patterns à la Miller but modulo β-equivalence only
(and not βη).

::

   rule diff (λx, sin $F[x]) ↪ λx, diff (λx, $F[x]) x × cos $F[x]

Patterns can contain abstractions ``λx, _`` and the user may attach an
environment made of *distinct* bound variables to a pattern variable to
indicate which bound variable can occur in the matched term. The
environment is a semicolon-separated list of variables enclosed in
square brackets ``[x;y;...]``. For instance, a term of the form
``λx y,t`` matches the pattern ``λx y,$F[x]`` only if ``y`` does not
freely occur in ``t``.

::

   rule lam (λx, app $F[] x) ↪ $F // η-reduction

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

   rule add (add x y) z ↪ add x (add y z)

They can overlap:

::

   rule add zero x ↪ x
   with add x zero ↪ x

And they can be non-linear:

::

   rule minus x x ↪ zero

Note that rewriting rules can also be defined simultaneously, using the
``with`` keyword instead of the ``rule`` keyword for all but the first
rule.

::

   rule add zero      $n ↪ $n
   with add (succ $n) $m ↪ succ (add $n $m)

Adding sets of rules allows to maintain confluence.

Examples of patterns are available in ``tests/OK/patterns.lp``.

``set declared|prefix|infix|quantifier|builtin|unif_rule``
----------------------------------------------------------

The ``set`` command is used to control the behaviour of Lambdapi and
extension points in its syntax.

**declared identifiers** The following code declares a new valid identifier.

::

   set declared "ℕ"
   set declared "α"
   set declared "β"
   set declared "γ"
   set declared "x₁"
   set declared "x₂"
   set declared "x₃"

**prefix symbols** The following code defines a prefix symbol for
negation.

::

   set prefix 5 "¬" ≔ neg

**infix symbols** The following code defines infix symbols for addition
and multiplication. Both are associative to the left, and they have
priority levels ``6`` and ``7`` respectively.

::

   set infix left 6 "+" ≔ add
   set infix left 7 "×" ≔ mul

The modifier ``infix``, ``infix right`` and ``infix left`` can be used
to specify whether the defined symbol is non-associative, associative to
the right, or associative to the left. The priority levels are floating
point numbers, hence a priority can (almost) always be inserted between
two different levels.

*WARNING:* some checks are performed upon the declaration of infix
symbols and identifiers, but they are by no means sufficient (it is
still possible to break the parser by defining well-chosen tokens).

**quantifier symbols** The representation of a symbol can be modified to
make it look like a usual quantifier (such as ``∀``, ``∃`` or ``λ``).
Symbols declared as quantifiers can be input using a “quantifier” syntax
and their printing is changed:

::

   set quantifier ∀ // : Π {a}, (T a → Prop) → Prop
   compute ∀ {a'} (λx:T a,p) // prints ∀x:T a,p
   compute ∀ (λx:T a, p) // prints ∀x,p
   type ∀x,p // quantifiers can be written as such

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

   set builtin "0"  ≔ zero // : N
   set builtin "+1" ≔ succ // : N → N

**unification rules** The unification engine can be guided using
*unification rules*. Given a unification problem ``t ≡ u``, if the
engine cannot find a solution, it will try to match the pattern
``t ≡ u`` against the defined rules (modulo commutativity of ≡)
and rewrite the problem to the
right-hand side of the matched rule. Variables of the RHS that do
not appear in the LHS are replaced by fresh metavariables on rule application.

Examples:

::

   set unif_rule Bool ≡ T $t ↪ $t ≡ bool
   set unif_rule $x + $y ≡ 0 ↪ $x ≡ 0; $y ≡ 0
   set unif_rule $a → $b ≡ T $c ↪ $a ≡ T $a'; $b ≡ T $b'; $c ≡ arrow $a' $b'

Thanks to the first unification rule, a problem ``T ?x ≡ Bool`` is
transformed into ``?x ≡ bool``.

*WARNING* This feature is experimental and there is no sanity check
performed on the rules.
