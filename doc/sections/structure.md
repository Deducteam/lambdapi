Structure of directories and files
----------------------------------

 * `src/`: source code of Lambdapi

   + utilities:

     - `extra.ml`: standard library extension
     - `files.ml`: filenames and paths management
     - `console.ml`: output and debugging utilities

   + file, command and tactic handling:

     - `lambdapi.ml`: main file
     - `compile.ml`: file parsing and compiling (.lpo files)
     - `handle.ml`: command handling
     - `tactics.ml`: tactic handling
     - `rewrite.ml`: rewrite tactic
     - `proof.ml`: proof state

   + terms, signatures, rewriting, unification and type-checking:

     - `terms.ml`: internal representation of terms
     - `basics.ml`: basic operations on terms
     - `print.ml`: pretty printing of terms
     - `tree_types.ml`: types and basic functions for decision trees
     - `treecstr.ml`: constraints used in decision trees
     - `dtree.ml`: compilation of rewrite rules to decision trees
     - `eval.ml`: rewriting engine
     - `unif.ml`: unification algorithm
     - `ctxt.ml`: typing contexts (maps variable -> type)
     - `infer.ml`: constraints-generating type inference and checking
     - `typing.ml`: type inference and checking
     - `sign.ml`: signatures/theories (sets of symbols and rules)

   + parsing and scoping:

     - `pos.ml`: source file position management
     - `syntax.ml`: abstract syntax
     - `parser.ml`: parser (convert the concrete syntax into the abstract syntax)
     - `env.ml`: maps identifier -> variable (and type)
     - `scope.ml`: convert the abstract syntax into terms
     - `pretty.ml`: pretty print the abstract syntax (used to convert old Dedukti files into Lambdapi files)

   + legacy parser:

     - `legacy_lexer.ml`: lexer for the old Dedukti syntax
     - `legacy_parser.ml`: interface of the parser for the old Dedukti syntax
     - `menhir_parser.ml`: parser using Menhir (http://gallium.inria.fr/~fpottier/menhir/)

   + property checking:

     - `sr.ml`: algorithm for checking subject reduction
     - `confluence.ml`: call a confluence checker by converting signatures into a TRS file
     - `termination.ml`: call a termination checker by converting signatures into an XTC file

   + interface to editors:

     - `pure.ml` and `pure.mli`: interface to the LSP server

 * `lp-lsp/`: source code of the Lambdapi LSP server (see https://microsoft.github.io/language-server-protocol/ and https://langserver.org/)

 * `tests/`: unit tests
   - `OK/`: tests that should succeed
   - `KO/`: tests that should fail

 * `examples/`: examples of Dedukti or Lambdapi files with no proofs

 * `proofs/`: examples of Lambdapi files with proofs

 * `tools/`:
   - `bench.ml`: to run finer benches on some libraries
   - `deps.ml`: gives the `#REQUIRE` commands that should be added at the beginning of a Dedukti file
   - `generate_tests.ml`: creates test files in `tests/OK` that can be
     parametrised
   - `listings.tex`: setup of the LaTeX package [listings](https://www.ctan.org/pkg/listings) for including Lambdapi code into a LaTeX document
   - `sanity_check.sh`: script checking some style guidelines below (called by `make sanity_check`)

 * `libraries/`: libraries of Dedukti files (see GNUmakefile)


