Overview of directories and files
=================================

*  ``docs/``: documentation in `ReStructured Text`_ format

   * ``docs/README.md``: introduction to the user manual and guidelines

*  ``editors/``: editor plugins for handling Lambdapi files

   *  ``emacs/``: code for Emacs
   *  ``vim/``: code for Vim
   *  ``vscode/``: code for VSCode

      *  ``.vscode/*.json``: config for launching and debugging the extension
      *  ``src/*.ts``: source code of the extension
      *  ``package.json``: manifest of the plugin
         (activation events, scripts, dependencies, …)
      *  ``tsconfig.json``: TypeScript configuration (directories, …)
      *  ``vscode.proposed.d.ts``: VSCode API (Microsoft file)
      *  ``lp.configuration.json``: specific characters
      *  ``syntaxes/lp.tmLanguage.json``: grammar of Lambdapi

*  ``libraries/``: libraries of Dedukti files (see ``GNUmakefile``)

* ``src/lplib/``: extension of the Ocaml standard library

  *  ``realpath.c``: C implementation of ``Filename.realpath``
  *  ``range_intf.ml``: module type of abstract intervals
  *  ``range.ml``: instance of ``range_intf`` with integer intervals
  *  ``rangeMap_intf.ml``: module type of abstract maps on intervals
  *  ``rangeMap.ml``: instance of ``rangeMap_intf`` using ``range``

* ``src/common/``: miscellaneous modules and libraries

  * ``pos.ml``: source file position management
  * ``console.ml``: output and debugging
  * ``module.ml``: filenames and paths management
  * ``package.ml``: management of package files ``lambdapi.pkg``

* ``src/parsing/``: parsing Dedukti and Lambdapi files

  *  ``syntax.ml``: abstract syntax
  *  ``pretty.ml``: pretty print the abstract syntax
     (used to convert Dedukti files into Lambdapi files)
  *  ``parser.ml``: interfaces for parsers
  *  ``lpLexer.ml``: lexer for Lambdapi syntax
  *  ``lpParser.mly``: parser for Lambdapi syntax
  *  ``dkLexer.mll``: lexer for Dedukti2 syntax
  *  ``dkParser.mly``: parser for Dedukti2 syntax

*  ``src/core/``: core of Lambdapi

  *  scoping:

      *  ``env.ml``: maps identifier -> variable and type
      *  ``pratt.ml``: parsing of applications wrt symbol notations
      *  ``scope.ml``: convert the abstract syntax into terms

  *  terms, signatures, rewriting, unification and type-checking:

      *  ``tree_types.ml``: types and basic functions for decision trees
      *  ``tree.ml``: compilation of rewriting rules to decision trees
      *  ``term.ml``: internal representation of terms
      *  ``libTerm.ml``: basic operations on terms
      *  ``ctxt.ml``: typing contexts (maps variable -> type)
      *  ``print.ml``: pretty printing of terms
      *  ``eval.ml``: rewriting engine
      *  ``infer.ml``: constraints generating type inference and checking
      *  ``unif_rule.ml``: ghost signature for unification rules
      *  ``unif.ml``: unification algorithm
      *  ``sign.ml``: compiled module signature (symbols and rules in a module)
      *  ``sig_state.ml``: signature under construction
      *  ``builtin.ml``: managing builtins

*  ``src/handle``: signature building

   *  ``query.ml``: handling of queries
      (commands that do not change the signature or the proof state)
   *  ``tactic.ml``: tactic handling
   *  ``inductive.ml``: generation of induction principles
   *  ``command.ml``: command handling      
   *  ``compile.ml``: file parsing and compiling (.lpo files)
   *  ``proof.ml``: proof state
   *  ``rewrite.ml``: rewrite tactic (similar to Ssreflect)
   *  ``why3_tactic.ml``: why3 tactic


*  ``src/tool/``: tools

   *  ``tree_graphviz.ml``: representation of trees as graphviz files
   *  ``external.ml``: call of external tools
   *  ``hrs.ml``: export to the .hrs format of the confluence competition
   *  ``xtc.ml``: export to the .xtc format of the termination competition
   *  ``sr.ml``: algorithm for checking subject reduction

*  ``src/cli/``: command line interface

   *  ``cliconf.ml``: main program configuration
   *  ``lambdapi.ml``: main program
   *  ``init_cmd.ml``: lambdapi init program
   *  ``install_cmd.ml``: lambdapi install command

*  ``src/pure/``: pure interface (mainly used by the LSP server)

   *  ``pure.ml``: provide utilities to roll back the state

*  ``src/lsp/``: LSP server

   *  ``lp_doc.ml``: document type
   *  ``lsp_base.ml``: basic functions for building messages
   *  ``lsp_io.ml``: basic functions for reading and sending messages
   *  ``lp_lsp.ml``: LSP server

*  ``tests/``: unit tests

   *  ``OK/``: tests that should succeed
   *  ``KO/``: tests that should fail

*  ``tools/``:

   *  ``gen_version.ml``: script used by dune to generate
      ``_build/default/src/core/version.ml`` used in ``lambdapi.ml``
   *  ``sanity_check.sh``: script checking some style guidelines below
      (called by ``make sanity_check``)
   *  ``generate_tests.ml``: creates test files in ``tests/OK`` that can
      be parametrised
   *  ``listings.tex``: setup of the LaTeX package
      `listings <https://www.ctan.org/pkg/listings>`__ for including
      Lambdapi code into a LaTeX document
   *  ``deps.ml``: gives the ``#REQUIRE`` commands that should be added
      at the beginning of a Dedukti file

.. _Sphinx: https://www.sphinx-doc.org/en/master/
.. _Restructured Text: https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html
