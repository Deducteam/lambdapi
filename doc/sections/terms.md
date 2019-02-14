Syntax of terms
---------------

The BNF grammar of Lambdapi is in [syntax.bnf](../syntax.bnf).

A user-defined term can be either:

 * `TYPE`
 
 * a possibly qualified identifier denoting either:

   - a symbol previously declared in the current file or in some previously open module
   - a symbol declared in some previously required module if it is qualified
   - a bound variable
   - a metavariable or goal

  Convention: identifiers starting with a capital letter denote types and predicates (e.g. `Nat`, `List`), and identifiers starting with a small letter denote constructors, functions and proofs (e.g. `zero`, `add`, `refl`).
  
 * an anonymous function `λ(x y:A) z,t` mapping `x`, `y` and `z` (of type `A` for `x` and `y`) to `t`

 * a dependent product `∀(x y:A) z,T`

 * a non-dependent product `A ⇒ T` (syntactic sugar for `∀x:A,T` with `x` not occurring in `T`)

 * a `let f (x y:A) z = t` construction

 * application is written by space-separated juxtaposition, except for symbol identifiers declared as infix (e.g. `x+y`)

 * `_` for an unknown term or a term we don't care about. It will be infered by the system or, inside a proof, replaced by a fresh metavariable generating a new subgoal.

 * an integer between 0 and 2^30-1 if the builtins "0" and "+1" are defined

Subterms can be parenthesized to avoid ambiguities.
