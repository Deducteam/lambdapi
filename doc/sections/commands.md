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

<!----------------------------------------------------------------------------> 
### Lexical conventions

TODO

<!----------------------------------------------------------------------------> 
### The `require` command

The `require` command informs the type-checker that the current module depends
on some other module, which must hence be compiled.
```
require boolean
require church.list as list
```
Note that a required module can optionally be aliased, in which case it can be
referred to with the provided name.

<!----------------------------------------------------------------------------> 
### The `open` command

The `open` command puts into scope the symbols defined in the given module. It
can also be combined with the `require` command.
```
open booleans
require open church.sums
```

<!----------------------------------------------------------------------------> 
### The `symbol` declaration command

Symbols are declared using the `symbol` command, possibly associated with some
modifier like `const` or `injective`.

```
symbol const Nat : TYPE
symbol const zero : Nat
symbol const succ (x:Nat) : Nat
symbol add : Nat ⇒ Nat ⇒ Nat
symbol const list : Nat ⇒ TYPE
symbol const nil : List zero
symbol const cons : Nat ⇒ ∀n, List n ⇒ List(succ n) 
```

The command requires a fresh symbol name (it should not have already been used
in the current module) and a type for the symbol.

It is possible to put arguments on the left side of the `:` symbol (similarly
to a value declaration in OCaml).

Data types and predicates must be given types of the form
`∀x1:T1,..,∀xn:Tn,TYPE`.
`T⇒U` is a shorthand for `∀x:T,U` when `x` does not occur in `U`.

We recommend to start types and predicates by a capital letter.

Modifiers:
 - `const`: no rule can be added to the symbol
 - `injective`: the symbol can be considered as injective, that is,
 if `f t1 .. tn` ≡ `f u1 .. un`, then `t1`≡`u1`, ..., `tn`≡`un`.
 For the moment, the verification is left to the user.

<!----------------------------------------------------------------------------> 
### The `rule` declaration command

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

Lambdapi accepts higher-order pattern variables too:

```
rule diff (λx, sin &F[x]) → λx, diff (λx, &F[x]) x × cos &F[x]
rule lam (λx, app &F x) → &F // η-reduction
```

Pattern variables can be applied to distinct bound variables only.

In left-hand side, λ-expressions must have no type annotations.

<!----------------------------------------------------------------------------> 
### The `definition` command

The `definition` command is used to immediately define a new symbol, for it to
be equal to some (closed) term.
```
definition plus_two : Nat ⇒ Nat ≔ λn,add n (succ (succ zero))
definition plus_two (n : Nat) : Nat ≔ add n (succ (succ zero))
definition plus_two (n : Nat) ≔ add n (succ (succ zero))
definition plus_two n ≔ add n (succ (succ zero))
```
Note that some type annotations can be omitted, and that it is possible to put
arguments on the left side of the `≔` symbol (similarly to a value declaration
in OCaml).

<!----------------------------------------------------------------------------> 
### The `theorem` command

TODO

<!----------------------------------------------------------------------------> 
### The `assert` and `assertnot` commands

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
### The `set` command

The `set` command is used to control the behaviour of Lambdapi, and to control
extension points in its syntax.  For instance,  the following commands set the
verbosity level to `1`,  enable the debugging flags `t` and `s`,  and disables
the debugging flag `s`.
```
set verbose 1
set debug +ts
set debug -s
```

The following code sets the definition of built-in symbols. They are used, for
example, to specify a zero and successor function for unary natural numbers so
that natural number literals can be automatically translated to their use.
```
set builtin "0"  ≔ zero
set builtin "+1" ≔ succ
```

The following code defines infix symbols for addition and multiplication. Both
are associative to the left, and they have priority levels `6` and `7`.
```
set infix left 6 "+" ≔ add
set infix left 7 "×" ≔ mul
```
The modifier `infix`, `infix right` and `infix left` can be used to specify
whether the defined symbol is non-associative, associative to the right,
or associative to the left. The priority levels are floating point numbers,
hence a priority can (almost) always be inserted between two different levels.

**Important limitation:** no check is done on the syntax of the symbol that is
defined. As a consequence, it is very easy to break the system by redefining a
keyword or a common symbol (e.g., `"("`, `")"` or `"symbol"`).
