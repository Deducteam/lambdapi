Overview of directories and files
=================================

*  ``docs/``: documentation in `ReStructured Text`_ format, to be built with
   `Sphinx`_.

   * ``docs/README.md``: introduction to the user manual and guidelines

*  ``editors/``: editor plugins for handling Lambdapi files

   *  ``emacs/``: code for emacs
   *  ``vim/``: code for vim
   *  ``vscode/``: code for vscode

      *  ``.vscode/*.json``: config for launching, debugging, building
         the extension
      *  ``src/*.ts``: the VSCode plugin source code written in the
         TypeScript language
      *  ``package.json``: the manifest of the plugin (activation
         events, scripts, dependencies, …)
      *  ``tsconfig.json``: TypeScript configuration (directories, …)
      *  ``vscode.proposed.d.ts``: VSCode API (Microsoft file, likely to
         change)
      *  ``lp.configuration.json``: specific characters
      *  ``syntaxes/lp.tmLanguage.json``: grammar of lambdapi
      *  ``Makefile``

*  ``libraries/``: libraries of Dedukti files (see GNUmakefile)

* ``src/lplib/``: extension of the Ocaml standard library

  *  ``realpath.c``: C implementation for ``Filename.realpath``
  *  ``range_intf.ml``: module type of abstract intervals
  *  ``range.ml``: instance of ``range_intf`` with integer intervals
  *  ``rangeMap_intf.ml``: module type of abstract maps on intervals
  *  ``rangeMap.ml``: instance of ``rangeMap_intf`` using ``range``

* ``src/common/``: miscellaneous modules and libraries

  * ``pos.ml``: source file position management
  * ``console.ml``: output and debugging
  * ``module.ml``: filenames and paths management
  * ``package.ml``: management of package files ``lambdapi.pkg``


* ``src/parsing/``: parsing dedukti and lambdapi files

  *  ``dkLexer.mll``: lexer for Dedukti2 syntax
  *  ``dkParser.mly``: parser for Dedukti2 syntax
  *  ``lpLexer.ml``: lexer for Lambdapi syntax using Sedlex
  *  ``parser.ml``: interfaces for parsers
  *  ``syntax.ml``: abstract syntax
  *  ``pretty.ml``: pretty print the abstract syntax (used to
     convert old Dedukti files into Lambdapi files)

*  ``src/core/``: source code of Lambdapi

   *  file, command and tactic handling:

      *  ``rewrite.ml``: rewrite tactic (similar to Ssreflect)
      *  ``why3_tactic.ml``: why3 tactic (uses
         `why3 <http://why3.lri.fr/>`__)
      *  ``proof.ml``: proof state

   *  terms, signatures, rewriting, unification and type-checking:

      *  ``term.ml``: internal representation of terms
      *  ``libTerm.ml``: basic operations on terms
      *  ``print.ml``: pretty printing of terms
      *  ``tree_types.ml``: types and basic functions for decision trees
      *  ``tree.ml``: compilation of rewriting rules to decision trees
      *  ``eval.ml``: rewriting engine
      *  ``unif.ml``: unification algorithm
      *  ``unif_rule.ml``: definition of *ad-hoc* symbols for unification rules
      *  ``ctxt.ml``: typing contexts (maps variable -> type)
      *  ``infer.ml``: constraints-generating type inference and
         checking
      *  ``sign.ml``: signatures/theories (sets of symbols and rules)
      *  ``sig_state.ml``: signature as a state in which symbols can be type
        checked

   *  scoping:

      *  ``env.ml``: maps identifier -> variable (and type)
      *  ``scope.ml``: convert the abstract syntax into terms

   *  property checking:

      *  ``sr.ml``: algorithm for checking subject reduction

*  ``src/handle``: use Lambdapi core to build signatures and type check terms

   *  ``tactic.ml``: tactic handling
   *  ``compile.ml``: file parsing and compiling (.lpo files)
   *  ``handle.ml``: command handling
   *  ``query.ml``: handling of queries (commands that do not
      change the signature or the proof state)

*  ``src/tool/``: tools using Lambdapi core

   *  ``tree_graphviz.ml``: representation of trees as graphviz files
   *  ``hrs.ml``: export to the .hrs format of the confluence
      competition
   *  ``xtc.ml``: export to the .xtc format of the termination
      competition
   *  ``external.ml``: call of external tools

*  ``src/cli/``: command line interface

   *  ``lambdapi.ml``: main program

*  ``src/pure/``: pure interface (mainly used by the LSP server)

   *  ``pure.ml`` and ``pure.mli``: provide utilities to roll back state

*  ``src/lsp/``: LSP server

*  ``tests/``: unit tests

   *  ``OK/``: tests that should succeed
   *  ``KO/``: tests that should fail

*  ``tools/``:

   *  ``deps.ml``: gives the ``#REQUIRE`` commands that should be added
      at the beginning of a Dedukti file
   *  ``generate_tests.ml``: creates test files in ``tests/OK`` that can
      be parametrised
   *  ``listings.tex``: setup of the LaTeX package
      `listings <https://www.ctan.org/pkg/listings>`__ for including
      Lambdapi code into a LaTeX document
   *  ``sanity_check.sh``: script checking some style guidelines below
      (called by ``make sanity_check``)
   *  ``gen_version.ml``: script used by dune to generate the
      ``src/core/version.ml`` file

.. _Sphinx: https://www.sphinx-doc.org/en/master/
.. _Restructured Text: https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html
