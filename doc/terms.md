Syntax of terms
---------------

The BNF grammar of Lambdapi is in [syntax.bnf](syntax.bnf).

A qualified identifier is an identifier of the form `dir1.`
... `dirn.file.id` denoting the function symbol `id` defined in the
file `dir1/` ... `/dirn/file.lp`. To be used, `dir1.` ... `dirn.file`
must be required first.

A user-defined term can be either:

 * `TYPE`

 * a possibly qualified identifier denoting either:

   - a qualified symbol or a non-qualified symbol previously declared in the current file or in some previously open module, possibly prefixed by `@` to disallow implicit arguments
   - a bound variable
   - a metavariable or goal when prefixed by `?`

  **Convention:** identifiers starting with a capital letter denote types and predicates (e.g. `Nat`, `List`), and identifiers starting with a small letter denote constructors, functions and proofs (e.g. `zero`, `add`, `refl`).

 * an anonymous function `λ(x:A) y z,t` mapping `x`, `y` and `z` (of type `A` for `x`) to `t`

 * a dependent product `Π(x:A) y z,T`

 * a non-dependent product `A → T` (syntactic sugar for `Πx:A,T` with `x` not occurring in `T`)

 * a `let f (x:A) y z: T ≔ t in` construction (with `let f x : A ≔ t in u` being a
   syntactic sugar for `let f : Πx:_ → A ≔ λx, t in u`)

 * application is written by space-separated juxtaposition, except for symbol identifiers declared as infix (e.g. `x+y`)

 * a meta-variable application `?M[t;u;v]`

 * a pattern-variable application `$M[x;y]` (in rules only)

 * `_` for an unknown term or a term we don't care about. It will be infered by the system or, inside a proof, replaced by a fresh metavariable generating a new subgoal. It is replaced by a metavariable (or a pattern variable in the case of a rule left-hand side) applied to all the variables of the context.

 * an integer between 0 and 2^30-1 if the builtins "0" and "+1" are defined (see the [`set`](commands.md) command)

Subterms can be parenthesized to avoid ambiguities.

In case of a the application of a function symbol, an implicit argument can be given by enclosing it between curly brackets `{` ... `}`.
