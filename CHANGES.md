All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## Unreleased

### Added

- CLI command `deindex` to remove constants from the index.
- Indexing of symbols from current development (as well as currently required files) and their deindexing when files are closed are now automatically supported.
- Added filtering of search results using regular expressions.
- Added support for basic Rocq syntax for writing search queries (fun, forall, exists, /\ and ~).
- Allow the `--require` flag to be used multiple times with the `search` and `websearch` commands.
- Ambiguity due to overloaded symbols is now solved by normalisation.



### Changed

- `simplify` now fails if the goal cannot be simplified.

## 3.0.0 (2025-07-16)

### Added

- Tactic `simplify rule off` to simplify the focused goal wrt β-reduction only.
- Tacticals `orelse` and `repeat`.
- Tactic `eval` which evaluates a term and interprets it as a tactic. This allows one to define tactics using rewriting.
- Builtin `"String"` for string literals between double quotes.
- Options `--header` and `--url` for the `websearch` command.
- In search queries, replace the substring `"forall"` and `"->"` by `"Π"` and `"→"` respectively.
- Websearch queries and responses are now recorded in the log.
- Commands `debug` and `flag` with no argument to get the list of debug flags and the list of flags respectively.
- Tactic `change`.
- Modifier `private` for `open` command to not be exported.

### Changed

- Replaced Bindlib by de Bruijn (Frédéric) and closures (Bruno). The performances are slightly better than with Bindlib, especially on rewriting intensive files (the new version is 3.7 times faster on `tests/OK/perf_rw_engine.lp`). Lambdapi is now 2 times faster than dkcheck on matita, and only 2 times slower than dkcheck on holide.
- Several improvements to use the search engine:
  * normalize queries in websearch/search
  * pre-load a file in websearch (e.g. to declare implicit args)
  * paginate the output in the generated webpage
  * allow to declare rewriting rules (e.g. alignments) over defined and constant symbols
  * improve error message for overloaded symbols
- Tactic set x ≔ t: replace all subterms equal to t by x.
- Enhance the formatting of the search results.
- `require` and `open` are now recursive.

### Fixed

- Notations on external symbols are now exported.
- Make the websearch server listen on all the interfaces instead of localhost only.

## 2.6.0 (2025-01-25)

### Added

- Add tactic `set`.
- Decimal notation for integers.
- add the `--db` option to the `index`, `search` and `websearch` commands

### Fixed

- Why3 tactic.
- Induction tactic.

### Changed

- Improved Core.Term.eq_modulo (Claudio Sacerdoti) -> speed up factor between 2 and 9.
- The export option `--requiring` does not require as argument a file with extension `.v` anymore: the argument must be a module name.
- Option '--erasing' renamed into '--mapping'.
- Builtins necessary for the decimal notation.

## 2.5.1 (2024-07-22)

### Added

- Add export format `raw_dk`.
- Fix of the color of the text in command line when console.out is used.
- Use black text instead of red when diplaying query answers.
- Allow negative numbers in notation priorities.
- New release 0.2.2 of the VSCode plugin.

## 2.5.0 (2024-02-25)

### Added

- Add the `opaque` command to turn a defined symbol into a constant.
- Add the tactic `try` that tries to apply a tactic to the focused goal.
  If the application of the tactic fails, it catches the error and leaves the goal unchanged.

### Fixed

- Coq export: do not rename module names
- Sequential symbols: fix order of rules

## 2.4.1 (2023-11-22)

### Added

- support for Pratter 3.0.0
- printing of unification and coercion rules

### Improved

- unification

### Fixed

- Coq export
- matita.sh script

## 2.4.0 (2023-07-28)

### Added

- Several options for export -o stt_coq.
- Tactic remove.
- Option --no-sr-check to disable subject reduction checking.
- CLI command index to build ~/.LPSearch.db.
- Indexed terms can be normalized wrt rules with the option --rules
  (note that this new option --rules could be used to implement the equivalent
  of dkmeta later).
- CLI command search and LP command search to send queries to the index.
- Query language.
- CLI command websearch to run a webserver that can answer search queries.
- Option --port to specify the port to use.

### Improved

- Output for export -o stt_coq.

### Changed

- Private definitions are not kept in memory and in lpo files anymore.
- The record type Eval.config is extended with a new field allowing to specify
  which dtree to use for each symbol.

## 2.3.1 (2023-03-13)

### Fixed

- Opaque definitions are not kept in memory and in lpo files anymore
- A few bug fixes.

### Changed

- Why3 dependency updated to 1.6.

## 2.3.0 (2023-01-03)

### Added

- Export to Coq.
- (API) the rewrite engine can match on the constant `TYPE`.
- Automatic coercion insertion mechanism.
  For example, the command `coerce_rule coerce Int Float $x ↪ FloatOfInt $x;`
  can be used to instruct Lambdapi to automatically coerce integers to floats
  using the function `FloatOfInt`.

### Fixed

- Generation of metavariables through the rewriting engine.
- Application of pattern variables in rewrite rules RHS in the Dedukti
  export.
- Dedukti export: invalid Dedukti module name were not brace-quoted,
  for instance, `#REQUIRE module-name.` could be exported, while `module-name`
  is not recognised by Dedukti2. It is now exported as `#REQUIRE {|module-name|}`,
  and symbols are exported as `{|module-name|}.foo`.
- HRS and XTC exports.

### Changed

- Do not propose installation of Emacs mode via opam anymore as it can easily be installed from Emacs.

## 2.2.1 (2022-07-04)

### Added

- Propagate recompile flag to dependencies.
- Postfix operators with the `notation <op> postfix <priority>;`

### Removed

- Logic directory since it is now available on the [Lambdapi Opam repository](https://github.com/Deducteam/opam-lambdapi-repository).
- Option --recompile.

### Changed

- Use short options in system commands to be POSIX compliant.

## 2.2.0 (2022-03-18)

### Added

- Incremental local confluence checking for non higher-order and non AC rules.
- Add options -o hrs and -o xtc to the export command.

### Changed

- `whnf` function takes a problem as argument and a list of tags that configure
  the rewriting. Tags may block beta reduction, block definition expansion or
  block rewriting.
- Do not print empty term environments `.[]`.
- Allow users to use the pattern variables `$0`, `$1`, etc. and internally name pattern variables by their index.
- Fixed debug flag printing in Pretty.
- Compatibility with Cmdliner 1.1.0 and Bindlib 6.0.0.

### Removed

- `tree_walk` is no longer in the API

## 2.1.0 (2022-01-17)

### Added

- In Logic/, a library of logics.

- The command export to translate signatures to the lp or dk files formats.

- New release of the VSCode extension.

- A small tutorial in tests/OK/tutorial.lp.

- The why3 tactic handles universal and existential quantifiers through
  two new builtins ("ex" and "all"). Codewise, it requires a new
  translation from encoded types to Why3 types.

- Terms may be _placeholders_. Placeholders are holes in the
  concrete syntax. They are refined into metavariables. *Placeholders
  cannot appear nonlinearly in terms*. From [A Bidirectional Refinement
  Algorithm...](https://arxiv.org/abs/1202.4905), p. 31,
  > Non linear placeholders are not allowed since two occurrences could be
  in contexts that bind different set of variables and instantiation with
  terms that live in one context would make no sense in the other one.

### Changed

- Moved the files tool/hrs.ml and tool/xtc.ml into the new export/ directory.

- Because placeholders are simple holes, the term `_ → _` is scoped
  into a full dependent product `Π x: M, N` where `N` is a metavariable
  that depend on `x` (see file `tests/OK/767.lp`)

- Type checking is slower following #696 because of refinement (not only
  the type but also the term must be destructured and rebuilt),
  |         | master | refiner |
  |---------|--------|---------|
  | holide  | 7:0    | 11:33   |
  | iprover | 5:58   | 6:50    |

### Removed

- The command beautify superseded by the new command export.

- Unused variable warning: whether a variable is used or not cannot be
  decided while scoping (following #696) since placeholders that do not
  depend on variables may be refined later into metavariables that may
  depend on them.

- Metavariables cannot be referenced by their name anymore, hence the
  syntax `?M.[x;y]` is obsolete, but `?0.[x;y]` isn't.

## 2.0.0 (2021-12-15)

### Release of the VSCode extension on the Marketplace (2021-12-10)

- Add `editors/vscode/CHANGES.md` and `editors/vscode/CONTRIBUTING.md`.
- Update documentation and README.md files.

### Structured proof scripts (2021-12-07)

A tactic replacing the current goal by n new goals must be followed by n proof scripts enclosed in curly brackets. For instance, instead of writing `induction; /* case 0 */ t1; ..; tm; /* case s */ q1; ..; qn`, we must now write `induction {t1; ..; tm} {q1; ..; qn}`.

Exception for tactics not really changing the current goal like "have": `/* proof of u */ have h: t; /* proof of t */ t1; ..; tm; /* proof of u continued */ q1; ..; qn` must now be written `have h: t {t1; ..; tm}; q1; ..; qn`.

Other modifications in the grammar:
- Curly brackets are reserved for proof script structuration.
- Implicit arguments must be declared using square brackets instead of curly brackets: we must write `[a:Set]` instead of `{a:Set}`.
- Term environments and rewrite patterns must be preceded by a dot: we must now write `$f.[x]` instead of `$f[x]`.
- The `focus` command is removed since it breaks structuration.

### Improve and simplify LP lexer (2021-12-07)

- allow nested comments (fix #710)
- replace everywhere `%S` by `\"%s\"`
- move checking compatibility with Bindlib of identifiers from lexer to scope
- move `is_keyword` from `lexer` to `pretty`
- move `package.ml` from `common/` to `parsing/`
- change `Config.map_dir` field type to `(Path.t * string) list`,
  `Library.add_mapping` type to `Path.t * string -> unit`
  and Compile.compile argument `lm` type to `Path.t * string`

### Update dkParser to be in sync with dkcheck (2021-11-30)

### Add option `--record-time` (2021-11-30)

### Improve evaluation and convertibility test (2021-06-02)

- fix `_LLet` by calling mk_LLet
- substitute arguments in TEnv's at construction time (mk_TEnv)
- improve eq_modulo to avoid calling whnf when possible
- use `Eval.pure_eq_modulo` in Infer and Unif (fix #693)

### Improve logs (2021-06-01)

- add Base.out = Format.fprintf
- uniformize printing code using Base.out
- rename oc arguments into ppf
- complete Term.pp_term
- improve some functions in Debug.D
- improve logging messages in Infer by adding a level argument

### Better handling of let's (2021-05-26)

- mk_LLet removes useless let's
- rename Eval.config into strat
- factorize whnf_beta and whnf
- fix handling of variable unfoldings in whnf_stk
- optimize context lookup by using a map
- gather problem, context, map and rewrite into a record data type
- abstract whnf in hnf, snf and eq_modulo
- fix typing of let's
- improve printing

### Interface Improvements (2021-05-20)

- Error messages are shown in logs buffer
- Improvements in behaviour of Emacs interface
- New shortcuts `C-c C-k` and `C-c C-r` for killing and reconnecting to the
  LSP server

### Record metavariable creation and instantiation during scoping, type inference and unification (2021-05-20)

- the record type problem gets a new field metas, and all its fields are now mutable
- many functions now take as argument a problem
- the functions infer_noexn, check_noexn and check_sort are moved to Query
  (they do not need to take a solver as argument anymore)
- in Unif, add_constr was defined twice; this is now fixed
- the modules Meta in Term and LibTerm are moved to the new file libMeta
- various mli files are created
- in Unif, initial is removed and instantiation is allowed to generate new constraints

### Bugfixes in rewriting engine (2021-05-06)

- Add tests on product matching
- Fixed scoping of product in LHS
- Wildcard created during tree compilation are the most general ones, any free
  variable may appear.
- Updated documentation of decision trees

### Factorize type `rw_patt` (2021-04-07)

The types `Term.rw_patt` and `Syntax.p_rw_patt_aux` are merged into a
single polymorphic type `Syntax.rw_patt`.

### API modification (2021-04-07)

Several functions are exposed,

- `Parsing.Scope.rule_of_pre_rule`: converts a pre rewriting rule into a
  rewriting rule,
- `Handle.Command.handle`: now processes proof data,
- `Handle.Command.get_proof_data`: is the old handle,
- `Handle.Compile.compile_with`: allows to provide a command handler to compile
  modules

### Add commutative and associative-commutative symbols (2021-04-07)

- Add `term.mli` and turn the `term` type into a *private* type so that
  term constructors are not exported anymore (they are available for
  pattern-matching though). For constructing terms, one now needs to
  use the provided construction functions `mk_Vari` for `Vari`,
  `mk_Appl` for `Appl`, etc.

- Move some functions `LibTerm` to `Term`, in particular `get_args`,
  `add_args` and `cmp_term`.

- Rename the field `sym_tree` into `sym_dtree`.

- Redefine the type `rhs` as `(term_env, term) Bindlib.mbinder`
  instead of `(term_env, term) Bindlib.mbinder * int` so that the old
  `rhs` needs to be replaced by `rhs * int` in a few places.

### Improvements in some tactics (2021-04-05)

- fix `have`
- improve the behavior of `apply`
- `assume` not needed before `reflexivity` anymore
- `assume` checks that identifiers are distinct
- `solve`: simplify goals afterwards
- `libTerm`: permute arguments of `unbind_name`, and add `add_args_map` and `unbind2_name`
- `syntax`: add `check_notin` and `check_distinct`
- split `misc/listings.tex` into `misc/lambdapi.tex` and `misc/example.tex`

### Extend command `inductive` to strictly-positive inductive types (2021-04-02)

### Renamings (2021-04-01)

- `./tools/` -> `./misc`
- `./src/core/tree_types.ml` -> `./src/core/tree_type.ml`

### Do not unescape identifiers anymore, and move `scope.ml` from `Core` to `Parsing` (2021-03-30)

- escaped regular identifiers are automatically unescaped in lexing
- unescaping is done in filenames only
- `Escape.add_prefix` and `Escape.add_suffix` allow to correctly extend potentially escaped identifiers
- move `scope.ml` from `Core` to `Parsing`

### Forbid bound variable names ending with a positive integer with leading zeros since there are not compatible with Bindlib (2021-03-29)

### Fix #341: remove spurious warnings on bound variables (2021-03-29)

* `scope.ml`:
  - the inner functions of scope are brought to the top-level
  - `scope_term_with_params` is introduced: it is similar to `scope_term` but does not check that top-level bound variables are used
  - `_Meta_Type` is moved to `env.ml` as `fresh_meta_type`

* `command.ml`:
  - use `scope_term_with_params` and check that parameters are indeed used
  - `get_implicitness` moved to `syntax.ml` as `get_impl_term`
  - fix implicit arguments computation in case of no type by introducing `Syntax.get_impl_params_list`

* in various places: use `pp_var` instead of `Bindlib.name_of`

* replace expo argument in scoping and handling by boolean telling if private symbols are allowed

* allow private symbols in queries

### Introduce `new_tvar = Bindlib.new_var mkfree` (2021-03-26)

### Add tactic `generalize`, and rename tactic `simpl` into `simplify` (2021-03-25)

### Use Dune for opam integration (2021-03-25)

- Content of `lambdapi.opam` is moved to `dune-project` and the former is
  generated using `dune build @install`.
- Vim files are installed in `opam` prefix using dune.
- The emacs mode is declared as a sub-package.

### Add tactic `have` (2021-03-24)

### Compatibility with Why3 1.4.0

### Add tactic `simpl <id>` for unfolding a specific symbol only (2021-03-22)

and slightly improve `Ctxt.def_of`

### Bug fixes (2021-03-22)

- fix type inference in the case of an application (t u) where the type of t is not a product yet (uncomment code commented in #596)
- fix the order in which emacs prints hypotheses
- fix opam dependencies: add constraint why3 <= 1.3.3

### Fix and improve inverse image computation (2021-03-16)

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

### Add tactic admit (2021-03-12)

- rename command `admit` into `admitted`
- `admitted`: admit the initial goal instead of the remaining goals (when the proof is an opaque definition)
- move code on `admit` from `command.ml` to `tactic.ml`
- add tactic `admit` (fix #380)
  As a consequence, tactics can change the signature state now.

### Improvements in type inference, unification and printing (2021-03-11)

- improve type inference and unification
- add flag `"print_meta_args"`
- print metavariables unescaped, add parentheses in domains
- replace `(current_sign()).sign_path` by `current_path()`
- improve logging:
  . debug +h now prints data on type inference/checking
  . provide time of type inference/checking and constraint solving
  . give more feedback when instantiation fails

### Remove `set` keyword (2021-03-04)

### Various bug fixes (2021-03-02)

- allow matching on abstraction/product type annotations (fix #573)
- Infer: do not check constraint duplication and return constraints in the order they have been added (fix #579)
- inductive type symbols are now declared as constant (fix #580)
- fix parsing and printing of unification rules
- Extra.files returns only the files that satisfy some user-defined condition
- tests/ok_ko.ml: test only .dk and .lp files
- Pretty: checking that identifiers are LP keywords is now optional (useful for debug)

### Fix notation declarations (2021-02-19)

- `set infix ... "<string>" := <qid>` is replaced by `set notation <qid> infix ...`
- `set prefix ... "<string>" := <qid>` is replaced by `set notation <qid> prefix ...`
- `set quantifier <qid>` is replaced by `set notation <qid> quantifier`
- the flag `print_meta_type` is renamed into `print_meta_types`
- `LibTerm.expl_args` is renamed into `remove_impl_args`

### Improve handling of ghost symbols and metavariable identifier (2021-02-18)

- Ghost paths and unification rule symbols managed in LpLexer now
  (no hard-coded strings anymore except for their definition)
- Allow users to type system-generated metavariable identifiers (integers)
- Fix printing of metavariable identifiers
- `key_counter` renamed into `meta_counter`
- `Meta.name` does not return a `?`-prefixed string anymore
- code factorization and reorganization in `query.ml`

### Improve navigation in Emacs/VSCode (2021-02-18)

- Electric mode for Emacs
- Buttons for Proof Navigation in Emacs
- Navigate by commands/tactics in Emacs and VScode
- Evaluated region shrinks on edit in Emacs and VScode
- Evaluated region changes colour after error in Emacs and VScode
- LSP server sends logs only from last command/tactic
- Few minor corrections in LSP server
- Improve VSCode indentation

### Add tactic induction (2021-02-17)

- `env.ml`: add functions for generating fresh metavariable terms
  (factorizes some code in `scope.ml` and `tactics.ml`)
- add fields in type `Sign.inductive` renamed into `ind_data`
- functions from `rewrite.ml` now take a `goal_typ` as argument
- code factorization in `tactic.ml`

- remove type aliases `p_type` and `p_patt`
- rename `P_Impl` into `P_Arro`, and `P_tac_intro` into `P_tac_assume`
- variable renamings in `sig_state`

### File renamings and splitting and better handling of escaped identifier (2021-02-12)

- File renamings and splittings:
  * `lpLexer` -> `escape`, `lpLexer`
  * `console` -> `base`, `extra`, `debug`, `error`, `console`
  * `module` -> `filename`, `path`, `library`
  * `cliconf` -> `config`
  * `install_cmd` -> `install`
  * `init_cmd` -> `init`

- Improve handling of escaped identifiers in `escape.ml` and fix printing

- Improve `tests/ok_ko.ml` to allow sub-directories in `tests/OK/` or `tests/KO/`

### File renamings and source code segmentation (2021-02-08)

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

### Add parameters to inductive definitions (2021-02-02)

### Parser (2021-01-30)

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


### Unification goals (2020-12-15)

changes in the syntax:
- definition -> symbol
- theorem -> opaque symbol
- proof -> begin
- qed -> end

### Mutually defined inductive types (2020-12-09)

### Inductive types (2020-09-29)

### Documentation in Sphinx (2020-07-31)

### Goals display in Emacs (2020-07-06)

### Sequential symbol (2020-07-06)

- Added `sequential` keyword for symbol declarations
- Removed `--keep-rule-order` option

### Change semantics of environments (2020-06-10)

- `$F` is shorthand for `$F[]`
- Empty environment mandatory under binders

### Add tactic `fail` (2020-05-26)

### Matching on products (2020-05-18)

Allow users to match on product `Πx: t, u` and on the domain of binders.

### Quantifier parsing and pretty-printing (2020-05-08)

- Allow users to declare a symbol [f] as quantifier. Then, [f x,t]
  stands for [f(λx,t)].

### Unification rules (2020-04-29)

Introduction of unification rules, taken from
<http://www.cs.unibo.it/~asperti/PAPERS/tphol09.pdf>.
A unification rule can be set with
```
set unif_rule t ≡ u ↪ v ≡ w, x ≡ y
```

### Pretty-printing (2020-04-25)

- Pretty-printing hints managed in signature state now.

### Syntax change (2020-04-16)

- `→` is replaced by `↪` in rewriting rules,
- `&` is replaced by `$` for pattern variables in rewriting rules,
- the syntax `rule ... and ...` becomes `rule ... with ...`,
- `⇒` is replaced by `→` for implication, and
- `∀` is replaced by `Π` for the dependent product type

### Let bindings (2020-03-31)

Adding let-bindings to the terms structure.
 - Contexts can now contain term definitions.
 - Unification is carried out with a context.
 - Reduction functions (`whnf`, `hnf`, `snf` &c.) are called with a context.
 - Type annotation for `let` in the concrete syntax.

### Prepare for modern versions of OCaml (2020-03-26)

- Use `Stdlib` instead of `Pervasives` (enforced by sanity checks).
- Rely on `stdlib-shims` to provide `Stdlib` on older version of OCaml.

### File management and module mapping (2020-03-20)

- New module system.
- Revised command line arguments parsing and introduce subcommands.
- LSP server is now a Lambdapi subcommand: run with `lambdapi lsp`.
- New `--no-warning` option (fixes #296).

### Trees simplification (2019-12-05)

Simplification of the decision tree structure
 - trees do not depend on term variables;
 - tree constructor type depends on generated at compile-time
   branch-wise unique integral identifiers;
 - graph output is more consistent: variables are the same in the
   nodes and the leaves.

### Protected symbols (2019-11-14)

Introducing protected and private symbols.

### Calling provers with Why3 (2019-10-29)

Introducing the `why3` tactic to call external provers.

### Eta equality as a flag (2019-10-21)

### Rewriting using decision trees (2019-09-17)

## 1.0.0 (2018-11-28)

First major release of Lambdapi. It introduces:
 - a new syntax for developing proofs in the system,
 - basic support for infix operators,
 - call to external confluence checker with the same API as Dedukti,
 - more things.
 - Consolidate the LSP OPAM package into the main one (@ejgallego)

## 0.1.0 (2018-09-19)

First release of Lambdapi.
