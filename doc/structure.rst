Overview of directories and files
=================================

* ``doc/``: documentation in `ReStructured Text`_ format

  * ``doc/README.md``: introduction to the user manual and guidelines

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

* ``libraries/``: libraries of Dedukti files (see ``Makefile``)

* ``src/cli/``: command line interface

  * ``config.ml``: main program configuration
  * ``init.ml``: lambdapi init command
  * ``install.ml``: lambdapi install command
  * ``lambdapi.ml``: main program

* ``src/common/``: miscellaneous modules and libraries

  * ``console.ml``: flag management
  * ``debug.ml``: debugging tools
  * ``error.ml``: warning and error management
  * ``escape.ml``: basic functions on escaped identifiers
  * ``library.ml``: Lambdapi library management
  * ``logger.ml``: logging tools
  * ``name.ml``: generation of fresh names
  * ``path.ml``: module paths in the Lambdapi library
  * ``pos.ml``: source file position management

* ``src/core/``: core of Lambdapi

  * terms:

    * ``term.ml``: internal representation of terms
    * ``libTerm.ml``: basic operations on terms
    * ``libMeta.ml``: basic operations on metavariables
    * ``print.ml``: pretty printing of terms
    * ``env.ml``: maps identifier -> variable and type
    
  * signatures:

    * ``builtin.ml``: managing builtins
    * ``sign.ml``: compiled module signature (symbols and rules in a module)
    * ``sig_state.ml``: signature under construction

  * rewriting:

    * ``tree_type.ml``: types and basic functions for decision trees
    * ``tree.ml``: compilation of rewriting rules to decision trees
    * ``eval.ml``: rewriting engine

  * type inference/checking:

    * ``ctxt.ml``: typing contexts (maps variable -> type)
    * ``infer.ml``: constraints generating type inference and checking

  * unification:

    * ``unif_rule.ml``: ghost signature for unification rules
    * ``unif.ml``: unification algorithm
    * ``inverse.ml``: inverse of injective functions

* ``src/export/``: export to other rule/proof formats

  * ``coq.ml``: export to Rocq
  * ``dk.ml``: export to Dedukti (after scoping and type-checking)
  * ``hrs.ml``: export to the .hrs format of the confluence competition
  * ``rawdk.ml``: export to Dedukti (before scoping and type-checking)
  * ``xtc.ml``: export to the .xtc format of the termination competition

* ``src/handle``: signature building

  * ``command.ml``: command handling
  * ``compile.ml``: file parsing and compiling (.lpo files)
  * ``inductive.ml``: generation of induction principles
  * ``query.ml``: handling of queries (commands that do not change the signature or the proof state)

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

  * pkg file parsing;
    
    * ``package.ml``: parsing of package files ``lambdapi.pkg``

  * abstract syntax:

    * ``syntax.ml``: abstract syntax
          
  * dk file parsing:
    
    * ``dkBasic.ml``: basic definitions for dk parsing
    * ``dkTokens.ml``: lexing tokens for dk syntax
    * ``dkLexer.mll``: lexer for dk syntax
    * ``dkRule.ml``: convert dk rules into lp rules
    * ``dkParser.mly``: parser for dk syntax

  * lp file parsing:
    
    * ``lpLexer.ml``: lexer for Lambdapi syntax
    * ``lpParser.mly``: parser for Lambdapi syntax
    * ``parser.ml``: interfaces for parsers
    * ``pretty.ml``: pretty print the abstract syntax (used to convert Dedukti files into Lambdapi files)

  * scoping:

    * ``pratt.ml``: parsing of applications wrt symbol notations
    * ``scope.ml``: convert the abstract syntax into terms

* ``src/pure/``: pure interface (mainly used by the LSP server)

  * ``pure.ml``: provide utilities to roll back the state

* ``src/tool/``: tools

  * ``external.ml``: call of external tools
  * ``indexing.ml``: indexation of symbols and rules
  * ``lcr.ml``: local confluence checking
  * ``sr.ml``: subject-reduction checking
  * ``tree_graphviz.ml``: representation of trees as graphviz files
  * ``websearch.eml.ml``: web server for searching theorems and rules

* ``tests/``: unit tests

  * ``OK/``: tests that should succeed
  * ``KO/``: tests that should fail

* ``misc/``:

  * ``deps.ml``: gives the ``#REQUIRE`` commands that should be added at the beginning of a Dedukti file
  * ``example.tex``: example of LaTeX file including Lambdapi code
  * ``generate_tests.ml``: creates test files in ``tests/OK`` that can be parametrised
  * ``gen_version.ml``: script used by dune to generate ``_build/default/src/core/version.ml`` used in ``lambdapi.ml``
  * ``git_hook_helper.sh``: script to run once to add a git hook to call ``sanity_check?sh`` before committing
  * ``lambdapi.tex``: setup of the LaTeX package `listings <https://www.ctan.org/pkg/listings>`__ for including Lambdapi code into a LaTeX document
  * ``sanity_check.sh``: script checking some style guidelines below (called by ``make sanity_check``)

.. _Sphinx: https://www.sphinx-doc.org/en/master/
.. _Restructured Text: https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html
