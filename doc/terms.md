Syntax of terms
---------------

/!\ PAGE UNDER DEVELOPMENT /!\

The BNF grammar of lambdapi can be found in [syntax.bnf](syntax.nf).

A user-defined term can be either:

 * `TYPE`
 
 * a possibly qualified identifier denoting either:

   - a symbol previously declared in the current file or in some previously open module
   - a symbol declared in some previously required module if it is qualified
   - a bound variable
   - a metavariable or goal

  Convention: an identifier starting with a capital letter for types and predicates, and a small letter for constructors, functions and proofs.
  
 * an anonymous function `λ(x y:A) z,t` mapping `x`, `y` and `z` (of type `A` for `x` and `y`) to `t`

 * a dependent product `∀(x y:A) z,T`

 * a `let f (x y:A) z = t` construction

 * application is written by space-separated juxtaposition, except for symbol identifiers declared as infix
 