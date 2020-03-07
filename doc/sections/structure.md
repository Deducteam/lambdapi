Structure of directories and files
----------------------------------

* `doc/`: documentation

     - `DOCUMENTATION.md`: entry point of the documentation, each topic being
        developed in a `.md` file of the `doc/sections` directory
     - `PERFS.md`: a comparison of performances of Dedukti 2.6 and Lambdapi
     - `syntax.bnf`: BNF grammar of Lambdapi

* `editors/`: editor plugins for handling Lambdapi files

   + `emacs/`: code for emacs
   + `vim/`: code for vim
   + `vscode/`: code for vscode

     - `.vscode/*.json`: config for launching, debugging, building the extension
     - `src/*.ts`: the VSCode plugin source code written in the TypeScript language
     - `package.json`: the manifest of the plugin (activation events, scripts, dependencies, ...)
     - `tsconfig.json`: TypeScript configuration (directories, ...)
     - `vscode.proposed.d.ts`: VSCode API (Microsoft file, likely to change)
     - `lp.configuration.json`: specific characters
     - `syntaxes/lp.tmLanguage.json`: grammar of lambdapi
     - `Makefile`
     - `.gitignore`

* `libraries/`: libraries of Dedukti files (see GNUmakefile)

* `lp-lsp/`: source code of the Lambdapi LSP server (see https://microsoft.github.io/language-server-protocol/ and https://langserver.org/)

* `src/core`: source code of Lambdapi

   + utilities:

     - `extra.ml`: standard library extension
     - `files.ml`: filenames and paths management
     - `pos.ml`: source file position management
     - `console.ml`: output and debugging
     - `external.ml`: call to external tools
     - `hrs.ml`: export to the .hrs format of the confluence competition
     - `xtc.ml`: export to the .xtc format of the termination competition
     - `config.ml`: handling of configuration files
     - `stubs.c`: C implementation for `Extra.Filename.realpath`.

   + file, command and tactic handling:

     - `compile.ml`: file parsing and compiling (.lpo files)
     - `handle.ml`: command handling
     - `queries.ml`: handling of queries (commands that do not change the signature or the proof state)
     - `tactics.ml`: tactic handling
     - `rewrite.ml`: rewrite tactic (similar to Ssreflect)
     - `why3_tactic.ml`: why3 tactic (uses [why3](http://why3.lri.fr/))
     - `proof.ml`: proof state

   + terms, signatures, rewriting, unification and type-checking:

     - `terms.ml`: internal representation of terms
     - `basics.ml`: basic operations on terms
     - `print.ml`: pretty printing of terms
     - `tree_types.ml`: types and basic functions for decision trees
     - `tree.ml`: compilation of rewriting rules to decision trees
     - `tree_graphviz.ml`: representation of trees as graphviz files
     - `eval.ml`: rewriting engine
     - `unif.ml`: unification algorithm
     - `ctxt.ml`: typing contexts (maps variable -> type)
     - `infer.ml`: constraints-generating type inference and checking
     - `typing.ml`: type inference and checking
     - `sign.ml`: signatures/theories (sets of symbols and rules)

   + parsing and scoping:

     - `syntax.ml`: abstract syntax
     - `parser.ml`: parser (convert the concrete syntax into the abstract syntax)
     - `env.ml`: maps identifier -> variable (and type)
     - `scope.ml`: convert the abstract syntax into terms
     - `pretty.ml`: pretty print the abstract syntax (used to convert old Dedukti files into Lambdapi files)

   + legacy parser:

     - `legacy_lexer.ml`: lexer for the old Dedukti syntax
     - `legacy_parser.ml`: interface of the parser for the old Dedukti syntax
     - `menhir_parser.ml`: parser using [menhir](http://gallium.inria.fr/~fpottier/menhir/)

   + property checking:

     - `sr.ml`: algorithm for checking subject reduction

* `src/pure`: pure interface (mainly used by the LSP server)

     - `pure.ml` and `pure.mli`: provide utilities to roll back state

* `src/lsp/`: files related to the LSP server

* `src/lambdapi.ml`: main program

* `tests/`: unit tests
   - `OK/`: tests that should succeed
   - `KO/`: tests that should fail

* `lib/`: a minimal standar library for Lambdapi.

* `tools/`:
   - `deps.ml`: gives the `#REQUIRE` commands that should be added at the beginning of a Dedukti file
   - `generate_tests.ml`: creates test files in `tests/OK` that can be parametrised
   - `listings.tex`: setup of the LaTeX package [listings](https://www.ctan.org/pkg/listings) for including Lambdapi code into a LaTeX document
   - `sanity_check.sh`: script checking some style guidelines below (called by `make sanity_check`)
   - `gen_version.ml`: script used by dune to generate the `src/core/version.ml` file
