Overview of directories and files
=================================

* ``docs/``: documentation in `ReStructured Text`_ format

   * ``docs/README.md``: introduction to the user manual and guidelines

* ``editors/``: editor plugins for handling Lambdapi files

   * ``emacs/``: code for Emacs
   * ``vim/``: code for Vim
   * ``vscode/``: code for VSCode

      * ``.vscode/*.json``: config for launching and debugging the extension
      * ``lp.configuration.json``: specific characters
      * ``media/styles.css``: styles
      * ``package.json``: manifest of the plugin
         (activation events, scripts, dependencies, …)
      * ``snippets/unicode.json``: short-cuts for entering unicode characters
      * ``src/*.ts``: source code of the extension
      * ``syntaxes/lp.tmLanguage.json``: grammar of Lambdapi
      * ``tsconfig.json``: TypeScript configuration (directories, …)
      * ``vscode.proposed.d.ts``: VSCode API (Microsoft file)
         <https://raw.githubusercontent.com/microsoft/vscode/master/src/vs/vscode.proposed.d.ts>

* ``libraries/``: libraries of Dedukti files (see ``GNUmakefile``)

* ``src/cli/``: command line interface

   * ``cliconf.ml``: main program configuration
   * ``init_cmd.ml``: lambdapi init program
   * ``install_cmd.ml``: lambdapi install command
   * ``lambdapi.ml``: main program

* ``src/common/``: miscellaneous modules and libraries

  * ``debug.ml``: debugging tools
  * ``console.ml``: flag management
  * ``escape.ml``: basic functions on escaped identifiers
  * ``library.ml``: Lambdapi library management
  * ``package.ml``: management of package files ``lambdapi.pkg``
  * ``path.ml``: module paths in the Lambdapi library
  * ``pos.ml``: source file position management

* ``src/core/``: core of Lambdapi

  * scoping:

      * ``env.ml``: maps identifier -> variable and type
      * ``pratt.ml``: parsing of applications wrt symbol notations
      * ``scope.ml``: convert the abstract syntax into terms

  * terms:

      * ``term.ml``: internal representation of terms
      * ``libTerm.ml``: basic operations on terms
      * ``print.ml``: pretty printing of terms

  * signatures:

      * ``builtin.ml``: managing builtins
      * ``sign.ml``: compiled module signature (symbols and rules in a module)
      * ``sig_state.ml``: signature under construction

  * rewriting:

      * ``tree_types.ml``: types and basic functions for decision trees
      * ``tree.ml``: compilation of rewriting rules to decision trees
      * ``eval.ml``: rewriting engine

  * type inference/checking:

      * ``ctxt.ml``: typing contexts (maps variable -> type)
      * ``infer.ml``: constraints generating type inference and checking

  * unification:

      * ``unif_rule.ml``: ghost signature for unification rules
      * ``unif.ml``: unification algorithm

* ``src/handle``: signature building

  * ``command.ml``: command handling
  * ``compile.ml``: file parsing and compiling (.lpo files)
  * ``inductive.ml``: generation of induction principles
  * ``query.ml``: handling of queries
      (commands that do not change the signature or the proof state)

  * tactics:

      * ``proof.ml``: proof state
      * ``rewrite.ml``: rewrite tactic (similar to Ssreflect)
      * ``tactic.ml``: tactic handling
      * ``why3_tactic.ml``: why3 tactic

* ``src/lplib/``: extension of the Ocaml standard library

  * ``range_intf.ml``: module type of abstract intervals
  * ``rangeMap_intf.ml``: module type of abstract maps on intervals
  * ``rangeMap.ml``: instance of ``rangeMap_intf`` using ``range``
  * ``range.ml``: instance of ``range_intf`` with integer intervals
  * ``realpath.c``: C implementation of ``Filename.realpath``

* ``src/lsp/``: LSP server

   * ``lp_doc.ml``: document type
   * ``lp_lsp.ml``: LSP server
   * ``lsp_base.ml``: basic functions for building messages
   * ``lsp_io.ml``: basic functions for reading and sending messages

* ``src/parsing/``: parsing Dedukti and Lambdapi files

  * ``dkLexer.mll``: lexer for Dedukti2 syntax
  * ``dkParser.mly``: parser for Dedukti2 syntax
  * ``lpLexer.ml``: lexer for Lambdapi syntax
  * ``lpParser.mly``: parser for Lambdapi syntax
  * ``parser.ml``: interfaces for parsers
  * ``pretty.ml``: pretty print the abstract syntax
     (used to convert Dedukti files into Lambdapi files)
  * ``syntax.ml``: abstract syntax

* ``src/pure/``: pure interface (mainly used by the LSP server)

   * ``pure.ml``: provide utilities to roll back the state

* ``src/tool/``: tools

   * ``external.ml``: call of external tools
   * ``hrs.ml``: export to the .hrs format of the confluence competition
   * ``sr.ml``: algorithm for checking subject reduction
   * ``tree_graphviz.ml``: representation of trees as graphviz files
   * ``xtc.ml``: export to the .xtc format of the termination competition

* ``tests/``: unit tests

   * ``OK/``: tests that should succeed
   * ``KO/``: tests that should fail

* ``tools/``:

   * ``gen_version.ml``: script used by dune to generate
      ``_build/default/src/core/version.ml`` used in ``lambdapi.ml``
   * ``sanity_check.sh``: script checking some style guidelines below
      (called by ``make sanity_check``)
   * ``generate_tests.ml``: creates test files in ``tests/OK`` that can
      be parametrised
   * ``listings.tex``: setup of the LaTeX package
      `listings <https://www.ctan.org/pkg/listings>`__ for including
      Lambdapi code into a LaTeX document
   * ``deps.ml``: gives the ``#REQUIRE`` commands that should be added
      at the beginning of a Dedukti file

.. _Sphinx: https://www.sphinx-doc.org/en/master/
.. _Restructured Text: https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html
