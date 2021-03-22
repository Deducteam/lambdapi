### Unreleased

#### Bug fixes (2021-03-22)

- fix type inference in the case of an application (t u) where the type of t is not a product yet (uncomment code commented in #596)
- fix the order in which emacs prints hypotheses
- fix opam dependencies: add constraint why3 <= 1.3.3

#### Fix and improve inverse image computation (2021-03-16)

- fix and improve in `inverse.ml` the computation of the inverse image of a term wrt an injective function (no unification rule is needed anymore in common examples, fix #342)
- fix management of "initial" constraints in unification (initial is now a global variable updated whenever a new constraint is added)
- when applying a unification rule, add constraints on types too (fix #466)
- turn `Infer.make_prod` into `Infer.set_to_prod`
- add pp_constrs for printing lists of constraints
- make time printing optional
- improve visualization of debugging data using colors:
  . blue: top-level type inference/checking
  . magenta: new constraint
  . green: constraint to solve
  . yellow: data from signature or context
  . red: instantiations (and handled commands)

#### Add tactic admit (2021-03-12)

- rename command `admit` into `admitted`
- `admitted`: admit the initial goal instead of the remaining goals (when the proof is an opaque definition)
- move code on `admit` from `command.ml` to `tactic.ml`
- add tactic `admit` (fix #380)
  As a consequence, tactics can change the signature state now.

#### Improvements in type inference, unification and printing (2021-03-11)

- improve type inference and unification
- add flag `"print_meta_args"`
- print metavariables unescaped, add parentheses in domains
- replace `(current_sign()).sign_path` by `current_path()`
- improve logging:
  . debug +h now prints data on type inference/checking
  . provide time of type inference/checking and constraint solving
  . give more feedback when instantiation fails

#### Remove `set` keyword (2021-03-04)

#### Various bug fixes (2021-03-02)

- allow matching on abstraction/product type annotations (fix #573)
- Infer: do not check constraint duplication and return constraints in the order they have been added (fix #579)
- inductive type symbols are now declared as constant (fix #580)
- fix parsing and printing of unification rules
- Extra.files returns only the files that satisfy some user-defined condition
- tests/ok_ko.ml: test only .dk and .lp files
- Pretty: checking that identifiers are LP keywords is now optional (useful for debug)

#### Fix notation declarations (2021-02-19)

- `set infix ... "<string>" := <qid>` is replaced by `set notation <qid> infix ...`
- `set prefix ... "<string>" := <qid>` is replaced by `set notation <qid> prefix ...`
- `set quantifier <qid>` is replaced by `set notation <qid> quantifier`
- the flag `print_meta_type` is renamed into `print_meta_types`
- `LibTerm.expl_args` is renamed into `remove_impl_args`

#### Improve handling of ghost symbols and metavariable identifier (2021-02-18)

- Ghost paths and unification rule symbols managed in LpLexer now
  (no hard-coded strings anymore except for their definition)
- Allow users to type system-generated metavariable identifiers (integers)
- Fix printing of metavariable identifiers
- `key_counter` renamed into `meta_counter`
- `Meta.name` does not return a `?`-prefixed string anymore
- code factorization and reorganization in `query.ml`

#### Improve navigation in Emacs/VSCode (2021-02-18)

- Electric mode for Emacs
- Buttons for Proof Navigation in Emacs
- Navigate by commands/tactics in Emacs and VScode
- Evaluated region shrinks on edit in Emacs and VScode
- Evaluated region changes colour after error in Emacs and VScode
- LSP server sends logs only from last command/tactic
- Few minor corrections in LSP server
- Improve VSCode indentation

#### Add tactic induction (2021-02-17)

- `env.ml`: add functions for generating fresh metavariable terms
  (factorizes some code in `scope.ml` and `tactics.ml`)
- add fields in type `Sign.inductive` renamed into `ind_data`
- functions from `rewrite.ml` now take a `goal_typ` as argument
- code factorization in `tactic.ml`

- remove type aliases `p_type` and `p_patt`
- rename `P_Impl` into `P_Arro`, and `P_tac_intro` into `P_tac_assume`
- variable renamings in `sig_state`

#### File renamings and splitting and better handling of escaped identifier (2021-02-12)

- File renamings and splittings:
  * `lpLexer` -> `escape`, `lpLexer`
  * `console` -> `base`, `extra`, `debug`, `error`, `console`
  * `module` -> `filename`, `path`, `library`
  * `cliconf` -> `config`
  * `install_cmd` -> `install`
  * `init_cmd` -> `init`

- Improve handling of escaped identifiers in `escape.ml` and fix printing

- Improve `tests/ok_ko.ml` to allow sub-directories in `tests/OK/` or `tests/KO/`

#### File renamings and source code segmentation (2021-02-08)

- File renamings:
  * `terms` -> `term`
  * `basics` -> `libTerm`
  * `tactics` -> `tactic`
  * `queries` -> `query`
  * `stubs` -> `realpath`
  * `files` -> `module`
  * `handle` -> `command`

- `Core` library divided into the following sub-libraries: 
  * `Common` that contains shared basic files
    (`pos`, `console`, `module` and `package`)
  * `Parsing` that contains everything related to parsing
    (`syntax`, `pretty`, lexers and parser)
  * `Handle` that uses `Core` to type check commands and modules 
    (contains `query`, `tactic`, `command`, `compile`, `inductive`, `rewrite`,
    `proof` and `why3_tactic`)
  * `Tool` that provides miscellaneous tools that use `Core`
    (`external`, `hrs`, `xtc`, `tree_graphviz`, `sr`)

#### Add parameters to inductive definitions (2021-02-02)

#### Parser (2021-01-30)

Replace Earley by Menhir, Pratter and Sedlex

Syntax modifications:

- Add multi-lines comments `/*` ... `*/`.

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

Code modifications:

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
