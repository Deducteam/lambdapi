Syntax of commands
------------------

The BNF grammar of Lambdapi is in [syntax.bnf](../syntax.bnf).

In this section, we will illustrate the syntax of Lambdapi using examples. The
first thing to note is that Lambdapi files are formed of a list of commands. A
command starts with a particular, reserved keyword.  And it ends either at the
start of a new command or at the end of the file.

<!---------------------------------------------------------------------------->
### Comments

One-line comments are introduced by '//':

```
// all this is ignored
```

In Emacs, one can (un)comment a region by using Meta-; .

<!---------------------------------------------------------------------------->
### Lexical conventions

TODO

<!---------------------------------------------------------------------------->
### `require`

The `require` command informs the type-checker that the current module depends
on some other module, which must hence be compiled.

```
require boolean
require church.list as list
```

Note that a required module can optionally be aliased, in which case it can be
referred to with the provided name.

<!---------------------------------------------------------------------------->
### `open`

The `open` command puts into scope the symbols defined in the given module. It
can also be combined with the `require` command.

```
open booleans
require open church.sums
```

<!---------------------------------------------------------------------------->
### `symbol`

Symbols are declared using the `symbol` command, possibly associated with some
modifier or an exposition marker. In the following example, `const` is a
modifier and `private` is an exposition marker.

```
symbol const Nat : TYPE
symbol const zero : Nat
symbol const succ (x:Nat) : Nat
symbol add : Nat ⇒ Nat ⇒ Nat
symbol const list : Nat ⇒ TYPE
symbol const nil : List zero
symbol const cons : Nat ⇒ ∀n, List n ⇒ List(succ n)
private symbol aux : ∀n, List n ⇒ Nat
```

The command requires a fresh symbol name (it should not have already been used
in the current module) and a type for the symbol.

It is possible to put arguments on the left side of the `:` symbol (similarly
to a value declaration in OCaml).

Data types and predicates must be given types of the form
`∀x1:T1,..,∀xn:Tn,TYPE`.

`T⇒U` is a shorthand for `∀x:T,U` when `x` does not occur in `U`.

We recommend to start types and predicates by a capital letter.

**Modifiers:**
 - `const`: no rule can be added to the symbol
 - `injective`: the symbol can be considered as injective, that is,
 if `f t1 .. tn` ≡ `f u1 .. un`, then `t1`≡`u1`, ..., `tn`≡`un`.
 For the moment, the verification is left to the user.

These modifiers are used to help the unification engine.

**Exposition marker**
Exposition defines how a symbol can be used outside the module where it is
defined. By default any symbol is _public_, which means it can be used without
restriction anywhere. There are two exposition markers available:
- `private`: the symbol cannot be used outside of its module (can be compared to
  a symbol not in the interface in OCaml);
- `protected`: the symbol can only be used in left-hand side of rewrite rules
  outside of its module.

Exposition obeys the following rules: inside a module,
- private symbols cannot appear in the type of public symbols;
- private symbols cannot appear in the right-hand side of a rewriting rule
  defining a public symbol
- externally defined protected symbols cannot appear at the head of a left-hand
  side
- externally defined protected symbols cannot appear in the right hand side of a
  rewriting rule

**Implicit arguments**. Some function symbol arguments can be declared
as implicit meaning that they must not be given by the user
later. Implicit arguments are replaced by `_` at parsing time,
generating a fresh metavariables. An argument declared as implicit can
be explicitly given by enclosing it between curly brackets `{` ... `}`
though. If a function symbol is prefixed by `@` then the implicit
arguments mechanism is disabled and all the arguments must be
explicitly given.

```
symbol eq {a:U} : T a ⇒ T a ⇒ Prop
// The first argument of `eq` is declared as implicit and must not be given
// unless `eq` is prefixed by `@`.
// Hence, [eq t u], [eq {_} t u] and [@eq _ t u] are all valid and equivalent.
```

**Infix notation**:
An infix notation can be declared for some symbol. See the command `set`.

<!---------------------------------------------------------------------------->
### `rule`

Rewriting rules for definable symbols are declared using the `rule` command.

```
rule add zero      &n → &n
rule add (succ &n) &m → succ (add &n &m)
```

Note that rewriting rules can also be defined simultaneously,  using the `and`
keyword instead of the `rule` keyword for all but the first rule.

```
rule add zero      &n → &n
and  add (succ &n) &m → succ (add &n &m)
```

Pattern variables need to be prefixed by `&`.

**Higher-order pattern-matching**.
Lambdapi accepts higher-order pattern variables too:

```
rule diff (λx, sin &F[x]) → λx, diff (λx, &F[x]) x × cos &F[x]
rule lam (λx, app &F x) → &F // η-reduction
```

In left-hand side, λ-expressions must have no type annotations.

Pattern variables can be applied to distinct bound variables only,
that is, the terms between `[` and `]` must be distinct bound
variables only.

Lambdapi uses higher-order pattern-matching (not in full generality
though). Hence, the rule `lam (λx, app &F x) → &F` implements
η-reduction since no valid instance of `F` can contain `x`.

**Important**. In contrast to languages like OCaml, Coq, Agda, etc. rule
 left-hand sides can contain defined symbols:

```
rule add (add x y) z → add x (add y z)
```

They can overlap:

```
rule add zero x → x
rule add x zero → x
```

And they can be non-linear:

```
rule minus x x → zero
```

<!---------------------------------------------------------------------------->
### `definition`

The `definition` command is used to immediately define a new symbol, for it to
be equal to some (closed) term. Definitions can use exposition markers the same
way the `symbol` command use them.

```
definition plus_two : Nat ⇒ Nat ≔ λn,add n (succ (succ zero))
definition plus_two (n : Nat) : Nat ≔ add n (succ (succ zero))
definition plus_two (n : Nat) ≔ add n (succ (succ zero))
definition plus_two n ≔ add n (succ (succ zero))
protected definition plus_two n ≔ add n (succ (succ zero))
```

Note that some type annotations can be omitted, and that it is possible to put
arguments on the left side of the `≔` symbol (similarly to a value declaration
in OCaml). Some arguments can be declared as implicit by enclosing them in
curly brackets.

<!---------------------------------------------------------------------------->
### `theorem`

The `theorem` command makes the user enter a new interactive mode. The
user has to provide a term of some given type. Such a goal is
materialized by a metavariable of the given type (goals and
metavariables are synonyms). One can then partially instantiate a goal
metavariable by using commands specific to this mode called tactics. A
tactic may generate new goals/metavariables. The proof of the theorem
is complete only when all generated goals have been solved.

[List of tactics](tactics.md)

<!---------------------------------------------------------------------------->
### `type`

The `type` command returns the type of a term.

```
symbol N : TYPE
symbol z : N
symbol s : N⇒N
type N⇒N // returns TYPE
type s z // returns N
```

<!---------------------------------------------------------------------------->
### `compute`

The `compute` command computes the normal form of a term.

```
symbol N : TYPE
symbol z : N
symbol s : N⇒N
symbol add : N⇒N⇒N
rule add z &x → &x
and add (s &x) &y → add &x (s &y)
compute add (s (s z)) (s (s z)) // returns s (s (s (s z)))
```

<!---------------------------------------------------------------------------->
### `assert` and `assertnot`

The `assert` and `assertnot` are convenient for checking that the validity, or
the invalidity, of typing judgments or convertibilities.  This can be used for
unit testing of Lambdapi, with both positive and negative tests.

```
assert zero : Nat
assert add (succ zero) zero ≡ succ zero
assertnot zero ≡ succ zero
assertnot succ : Nat
```

<!---------------------------------------------------------------------------->
### `set`

The `set` command is used to control the behaviour of Lambdapi and
extension points in its syntax.

**verbose level** The verbose level can be set to an integer between 0
and 3. Higher is the verbose level, more details are printed.

```
set verbose 1
```

**debug mode** The user can activate (with `+`) or deactivate (with
`-`) the debug mode for some functionalities as follows:

```
set debug +ts
set debug -s
```

Each functionality is represented by a single character. For instance,
`i` stands for type inference. To get the list of debuggable functionalities,
run the command `lambdapi --help`.

**flags** The user can set/unset some flags:

```
set flag "print_implicits" on // default is off
set flag "print_domains" on // default is off
set flag "eta_equality" on // default is off
```

**notation for natural numbers** It is possible to use the standard
decimal notation for natural numbers by specifying the symbols
representing 0 and the successor function as follows:

```
set builtin "0"  ≔ zero // : N
set builtin "+1" ≔ succ // : N ⇒ N
```

**infix symbols** The following code defines infix symbols for
addition and multiplication. Both are associative to the left, and
they have priority levels `6` and `7`.

```
set infix left 6 "+" ≔ add
set infix left 7 "×" ≔ mul
```

The modifier `infix`, `infix right` and `infix left` can be used to specify
whether the defined symbol is non-associative, associative to the right,
or associative to the left. The priority levels are floating point numbers,
hence a priority can (almost) always be inserted between two different levels.

**Prover config**:
In order to use the `why3` tactic, a prover should be set using:
```
set prover "Eprover"
```
*Alt-Ergo* is set by default if the user didn't specify a prover.

The user can also specify the timeout (in seconds) of the prover:
```
set prover_timeout 60
```
The default time limit of a prover is set to 2 seconds.

**prefix symbols** The following code defines a prefix symbol for negation.

```
set prefix 5 "¬" ≔ neg
```

**declared identifiers** The following code declares a new valid symbol, that
can then be used in the place of a symbol or variable.

```
set declared "ℕ"
set declared "α"
set declared "β"
set declared "γ"
set declared "x₁"
set declared "x₂"
set declared "x₃"
```

**Warning:** some checks are performed upon the declaration of infix symbols
and identifiers, but they are by no means sufficient (it is still possible to
break the parser by defining well-chosen tokens).

**equality-related builtins** In order to use tactics related to
Leibniz equality, one first has to define a number of builtin symbols
as follows:

```
set builtin "T"     ≔ T     // : U ⇒ TYPE
set builtin "P"     ≔ P     // : Prop ⇒ TYPE
set builtin "eq"    ≔ eq    // : ∀ {a}, T a ⇒ T a ⇒ Prop
set builtin "refl"  ≔ refl  // : ∀ {a} (x:T a), P (x=x)
set builtin "eqind" ≔ eqind // : ∀ {a} x y, P (x = y) ⇒ ∀ (p:T a⇒Prop), P (p y) ⇒ P (p x)
```
