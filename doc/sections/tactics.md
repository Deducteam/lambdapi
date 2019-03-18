Syntax of proof tactics
-----------------------

The BNF grammar of Lambdapi is in [syntax.bnf](../syntax.bnf).

The `theorem` command makes the user enter a new interactive mode. The
user has to provide a term of some given type. Such a goal is
materialized by a metavariable of the given type (goals and
metavariables are synonyms). One can then partially instantiate a goal
metavariable by using commands specific to this proof mode called
tactics. A tactic may generate new goals/metavariables. The proof of
the theorem is complete only when all generated goals have been
solved.

<!---------------------------------------------------------------------------->
### `print`

The `print` command displays the list of current goals. The first one
is called the focused goal. Tactics apply to the focused goal.

<!---------------------------------------------------------------------------->
### `qed`

The `qed` command allows one to quit the proof mode when all goals
have been solved. It then adds in the environment a new opaque
definition whose type is the theorem statement.

<!---------------------------------------------------------------------------->
### `admit`

The `admit` command allows one to quit the proof mode even if all
goals have not been solved. It then adds in the environment a new
symbol (axiom) whose type is the theorem statement.

<!---------------------------------------------------------------------------->
### `abort`

The `abort` command allows one to quit the proof mode without changing
the environment.

<!---------------------------------------------------------------------------->
### `focus`

The `focus` command allows the user to change the focus to another
goal. A goal is identified by its number in the list of goals
displayed by the `print` command.

<!---------------------------------------------------------------------------->
### `simpl`

The `simpl` tactic normalizes the focused goal with respect to
β-reduction and the user-defined rewriting rules.

<!---------------------------------------------------------------------------->
### `refine`

The tactic `refine t` tries to instantiate the current goal by the
term `t`. `t` can contain references to other goals by using `?n`
where `n` is a goal number or a goal name. `t` can contain underscores
`_` or new metavariable names `?n` which will be replaced by new
metavariables. The unification and type-checking algorithms will then
try to instantiate some of the generated metavariables. The
metavariables that cannot be solved are added as new goals.

<!---------------------------------------------------------------------------->
### `intro`

The tactic `intro h1 .. hn` replaces a goal of type `∀x1
.. xn,T` by a goal of type `T` with `xi` replaced by `hi`.

<!---------------------------------------------------------------------------->
### `apply`

The tactic `apply t` replaces a goal of type `T` by possibly new
goals `?0` of type `TO`, ..., `?n` of type `Tn` if `t` is of type
`∀x1:T1,..,∀xn:Tn,?0` and `t ?1 .. ?n` is of type `T`.

<!---------------------------------------------------------------------------->
### Tactics on equality

The tactics `refl`, `sym` and `rewrite` below assumes the existence of
symbols `T`, `P`, `eq` (with infix notation `=`), `eqind` and `refl`
with the following types and builtin declarations:

```
symbol T : U ⇒ TYPE
symbol P : Prop ⇒ TYPE
symbol eq {a} : T a ⇒ T a ⇒ Prop
symbol refl {a} (x:T a) : P (x = x)
symbol eqind {a} x y : P (x = y) ⇒ ∀(p:T a⇒Prop), P (p y) ⇒ P (p x)

set builtin "T"     ≔ T
set builtin "P"     ≔ P
set builtin "eq"    ≔ eq
set builtin "refl"  ≔ refl
set builtin "eqind" ≔ eqind
```

<!---------------------------------------------------------------------------->
### `refl`

The tactic `refl` solves a goal of the form `P (t = u)` when `t ≡ u`.

<!---------------------------------------------------------------------------->
### `sym`

The tactic `sym` replaces a goal of the form `P (t = u)` by the goal
`P (u = t)`.

<!---------------------------------------------------------------------------->
### `rewrite`

When `t` is a term of type `∀x1 .. xn,P(l=r)` and `u` is a subterm of
the focused goal matching `l`, that is, of the form `l` with `x1`
replaced by `u1`, ..., `xn` replaced by `un`, the tactic `rewrite t`
replaces in the focused goal `u` by the term `r` with `x1` replaced by
`u1`, ..., `xn` replaced by `un`.

The `rewrite` tactic accepts modifiers following the SSReflect syntax
   and semantics. See [A Small Scale Reflection Extension for the Coq
   system](http://hal.inria.fr/inria-00258384), by Georges Gonthier,
   Assia Mahboubi and Enrico Tassi, INRIA Research Report 6455, 2016,
   section 8, p. 48, for more details.
