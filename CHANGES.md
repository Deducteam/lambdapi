### Unreleased

#### Parser (2021-01-30)

Replace Earley by Menhir, Pratter and Sedlex

**Syntax modifications:**

- Commands and tactics must now be ended by a semi-colon `;`.

- The syntax `λx y z: nat, ...` with multiple variables is not
  authorised anymore, but `λ(x y z: nat), ...` is, as well as `λ x :
  N, t` with a single variable.

- In unification rules, the right hand-side must now be enclosed between square brackets, so
  ```
  set unif_rule $x + $y ≡ 0 ↪ $x ≡ 0; $y ≡ 0
  ```
  becomes
  ```
  set unif_rule $x + $y ≡ 0 ↪ [ $x ≡ 0; $y ≡ 0 ];
  ```
- `set declared` has been removed.

- Any (depending on accepted codepoints) UTF8 identifier is by default
  valid.
  *Warning:* string `λx` is now a valid identifier. Hence, expression `λx, t`
  isn't valid, but `λ x, t` is.

- Declared quantifiers now need a backquote to be applied. The syntax 
  `` `f x, t`` represents `f (λ x, t)` (and a fortiori `f {T} (λ x, t)`).

- `assert` always takes a turnstile (or vdash) to specify a (even
  empty) context, so the syntax is `assert ⊢ t: A;`

- The minus sign `-` in the rewrite tactic has been replaced by the
  keyword `left`.

**Code modifications:**

- Parsing and handling are interleaved (except in the LSP server): the
  parser returns a stream of parsed commands. Requesting an item of
  the stream parses one command in the file.
  
- The type `pp_hint` is renamed to `notation` and moved to `sign.ml`.
  
- Notations (that is, ex-`pp_hint`) are kept in a `SymMap`, which allowed to
  simplify some code in `sig_state.ml` and `sign.ml`.
  
- Positions are not lazy anymore, because Sedlex doesn't use lazy positions.

- `p_terms` do not have `P_BinO` and `P_UnaO` constructors anymore.


#### Unification goals (2020-12-15)

changes in the syntax:
- definition -> symbol
- theorem -> opaque symbol
- proof -> begin
- qed -> end

#### Mutually defined inductive types (2020-12-09)

#### Inductive types (2020-09-29)

#### Documentation in Sphinx (2020-07-31)

#### Goals display in Emacs (2020-07-06)

#### Sequential symbol (2020-07-06)

- Added `sequential` keyword for symbol declarations
- Removed `--keep-rule-order` option

#### Change semantics of environments (2020-06-10)

- `$F` is shorthand for `$F[]`
- Empty environment mandatory under binders

#### Add tactic `fail` (2020-05-26)

#### Matching on products (2020-05-18)

Allow users to match on product `Πx: t, u` and on the domain of binders.

#### Quantifier parsing and pretty-printing (2020-05-08)

- Allow users to declare a symbol [f] as quantifier. Then, [f x,t]
  stands for [f(λx,t)].

#### Unification rules (2020-04-29)

Introduction of unification rules, taken from
<http://www.cs.unibo.it/~asperti/PAPERS/tphol09.pdf>.
A unification rule can be set with
```
set unif_rule t ≡ u ↪ v ≡ w, x ≡ y
```

#### Pretty-printing (2020-04-25)

- Pretty-printing hints managed in signature state now.

#### Syntax change (2020-04-16)

- `→` is replaced by `↪` in rewriting rules,
- `&` is replaced by `$` for pattern variables in rewriting rules,
- the syntax `rule ... and ...` becomes `rule ... with ...`,
- `⇒` is replaced by `→` for implication, and
- `∀` is replaced by `Π` for the dependent product type

#### Let bindings (2020-03-31)

Adding let-bindings to the terms structure.
 - Contexts can now contain term definitions.
 - Unification is carried out with a context.
 - Reduction functions (`whnf`, `hnf`, `snf` &c.) are called with a context.
 - Type annotation for `let` in the concrete syntax.

#### Prepare for modern versions of OCaml (2020-03-26)

- Use `Stdlib` instead of `Pervasives` (enforced by sanity checks).
- Rely on `stdlib-shims` to provide `Stdlib` on older version of OCaml.

#### File management and module mapping (2020-03-20)

- New module system.
- Revised command line arguments parsing and introduce subcommands.
- LSP server is now a Lambdapi subcommand: run with `lambdapi lsp`.
- New `--no-warning` option (fixes #296).

#### Trees simplification (2019-12-05)

Simplification of the decision tree structure
 - trees do not depend on term variables;
 - tree constructor type depends on generated at compile-time
   branch-wise unique integral identifiers;
 - graph output is more consistent: variables are the same in the
   nodes and the leaves.
   
#### Protected symbols (2019-11-14)

Introducing protected and private symbols.

#### Calling provers with Why3 (2019-10-29)

Introducing the `why3` tactic to call external provers.

#### Eta equality as a flag (2019-10-21)

#### Rewriting using decision trees (2019-09-17)

### 1.0 (2018-11-28)

First major release of Lambdapi. It introduces:
 - a new syntax for developing proofs in the system,
 - basic support for infix operators,
 - call to external confluence checker with the same API as Dedukti,
 - more things.
 - Consolidate the LSP OPAM package into the main one (@ejgallego)

### 0.1 (2018-09-19)

First release of Lambdapi.
