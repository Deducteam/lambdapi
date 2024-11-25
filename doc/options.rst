Command line interface
======================

The main Lambdapi executable is called ``lambdapi``, and it can be
invoked using ``lambdapi COMMAND ...``. To see the list of the supported
commands, simply run ``lambdapi help`` or ``lambdapi --help``. To get
the documentation of a specific command run ``lambdapi COMMAND --help``.
It will contain the list of options that are supported by the command.

The available commands are:

* ``check``: check the correctness of input files.
* ``decision-tree``: output the decision tree of a symbol as a Dot graph (see :doc:`dtrees`)
* ``export``: translate the input file to other formats.
* ``help``: display the main help message.
* ``index``: create an index of symbols and rules of input files.
* ``init``: create a new Lambdapi package (see :doc:`getting_started`).
* ``install``: install the specified files according to package configuration.
* ``lsp``: run the Lambdapi LSP server.
* ``parse``: parse the input files.
* ``search``: runs a search query against the index.
* ``uninstall``: uninstalls the specified package.
* ``version``: give the current version of Lambdapi.
* ``websearch``: starts a webserver to search the library.

The commands ``parse``, ``export`` and ``index`` can trigger the
compilation of dependencies if the required object files (``.lpo``
extension) are not present.

**Input files:**

The commands ``check``, ``parse``, ``export`` and ``index`` expect input files
with either the ``.lp`` extension or the ``.dk`` extension.
The appropriate parser is selected automatically. The ``export`` command accept only one file as argument.

If a command takes several files as argument, the files are
handled independently in the order they are given. The program
immediately stops on the first failure, without going to the next file
(if any).

**Remark on index:**

The ``index`` command generates the file ``~/.LPSearch.db``. This file contains an indexation of all the symbols and rules occurring in the dk/lp files given in argument. By default, the file ``~/.LPSearch.db`` is erased first. To append new symbols and rules, use the option ``--add``. It is also possile to normalize terms wrt some rules before indexation by using ``--rules`` options.

**Remark on search:**

The command ``search`` takes as argument a query and runs it against the index file ``~/.LPSearch.db``. See :doc:`query_language` for the specification of the query language.

**Common flags:**

The commands ``check``, ``decision-tree``, ``export``, ``parse``,
``lsp`` all support the following command line arguments and flags.

* ``--debug=<FLAGS>`` enables the debugging modes specified by every character of ``FLAGS``. Details on available character flags are obtained using ``--help``.

* ``--lib-root=<DIR>`` sets the library root, that is, the folder corresponding to the entry point of the Lambdapi package system. This is the folder under which every package is installed, and a default value is only known if the program has been installed. In development mode, ``--lib-root lib`` must be given (assuming Lambdapi is run at the root of the repository).

* ``--map-dir=<MOD>:<DIR>`` maps an arbitrary directory ``DIR`` under a module path ``MOD`` (relative to the root directory). This option is mainly useful during the development of a package (before it has been installed). However it can also be accessed using a package configuration file (``lambdapi.pkg``) at the root of the library’s source tree. More information on that is given in the section about the module system.

* ``--no-sr-check`` disables subject reduction checking.

* ``--timeout=<NUM>`` gives up type-checking after the given number of seconds.  Note that the timeout is reset between each file, and that the parameter of the command is expected to be a natural number.

* ``-v <NUM>``, ``--verbose=<NUM>`` sets the verbosity level to the given natural number (the default value is 1). A value of 0 should not print anything, and the higher values print more and more information.

check
-----

* ``-c``, ``--gen-obj`` instructs Lambdapi to generate object files for every checked module (including dependencies). Object files have the extension ``.lpo`` and they are automatically read back when necessary if they exist and are up to date (they are regenerated otherwise).

* ``--too-long=<FLOAT>`` gives a warning for each interpreted source file command taking more than the given number of seconds to be checked. The parameter ``FLOAT`` is expected to be a floating point number.

export
------

* ``-o <FMT>``, ``--output=<FMT>`` instructs Lambdapi to translate the files given in argument according to ``<FMT>``:

  - ``lp``: Lambdapi format
  - ``dk``:  `Dedukti <https://github.com/Deducteam/dedukti>`__ format
  - ``raw_dk``:  `Dedukti <https://github.com/Deducteam/dedukti>`__ format
  - ``hrs``: `HRS <http://project-coco.uibk.ac.at/problems/hrs.php>`__ format of the confluence competition
  - ``xtc``: `XTC <https://raw.githubusercontent.com/TermCOMP/TPDB/master/xml/xtc.xsd>`__ format of the termination competition
  - ``raw_coq``: `Coq <https://coq.inria.fr/>`__ format
  - ``stt_coq``: `Coq <https://coq.inria.fr/>`__ format assuming that the input file is in an encoding of simple type theory

**WARNING**: With the formats ``raw_coq``, ``stt_coq`` and ``raw_dk``, the translation is done just after parsing, thus before scoping and elaboration. So Lambdapi cannot translate any input file, and the output may be incomplete or fail to type-check.

The format ``raw_dk`` does not accept the commands ``notation`` and ``inductive``, and proofs and tactics, which require elaboration.

The formats ``raw_coq`` and ``stt_coq`` only accept the commands ``require``, ``open``, ``symbol`` and ``rule``, but rules are simply ignored. The encoding of simple type theory can however be defined in Coq using `STTfa.v <https://github.com/Deducteam/lambdapi/blob/master/libraries/sttfa.v>`__.

For the format ``stt_coq``, several other options are available:

* ``--encoding <LP_FILE>`` (mandatory option) where ``<LP_FILE>`` contains the following sequence of builtin declarations:

::

   builtin "Set" ≔ ...; // : TYPE
   builtin "prop" ≔ ...; // : Set
   builtin "arr" ≔ ...; // : Set → Set → Set
   builtin "El" ≔ ...; // : Set → TYPE
   builtin "Prf" ≔ ...; // : El prop → TYPE
   builtin "eq" ≔ ...; // : Π [a : Set], El a → El a → El prop
   builtin "not" ≔ ...; // : El prop → El prop
   builtin "imp" ≔ ...; // : El prop → El prop → El prop
   builtin "and" ≔ ...; // : El prop → El prop → El prop
   builtin "or" ≔ ...; // : El prop → El prop → El prop
   builtin "all" ≔ ...; // : Π [a : Set], (El a → El prop) → El prop
   builtin "ex" ≔ ...; // : Π [a : Set], (El a → El prop) → El prop

It tells Lambdapi which symbols of the input files are used for the encoding. Example: `encoding.lp <https://github.com/Deducteam/lambdapi/blob/master/libraries/encoding.lp>`__. The first argument ``a`` of the symbols corresponding to the builtins ``"eq"``, ``"all"`` and ``"ex"`` need not be declared as implicit.

In symbol declarations or definitions, parameters with no type are assumed to be of type the term associated with the builtin ``"Set"``.

* ``--no-implicits`` instructs Lambdapi that the symbols of the encoding have no implicit arguments.

* ``--renaming <LP_FILE>`` where ``<LP_FILE>`` contains a sequence of builtin declarations of the form

::
   
   builtin "coq_expr" ≔ lp_id;

It instructs Lambdapi to replace any occurrence of the unqualified identifier ``lp_id`` by ``coq_expr``, which can be any Coq expression. Example: `renaming.lp <https://github.com/Deducteam/lambdapi/blob/master/libraries/renaming.lp>`__.

* ``--requiring <MODNAME>`` to add ``Require Import <MODNAME>`` at the beginning of the output. ``<MODNAME>.v`` usually needs to contain at least the following definitions:

::

   Definition arr (A:Type) (B:Type) := A -> B.
   Definition imp (P Q: Prop) := P -> Q.
   Definition all (A:Type) (P:A->Prop) := forall x:A, P x.

if the symbols corresponding to the builtins ``"arr"``, ``"imp"`` and ``"all"`` occurs partially applied in the input file. Example: `coq.v <https://github.com/Deducteam/lambdapi/blob/master/libraries/coq.v>`__.

* ``--erasing <LP_FILE>`` where ``<LP_FILE>`` contains a sequence of builtin declarations like for the option ``--renaming`` except that, this time, ``lp_id`` can be a qualified identifier. It has the same effect as the option ``--renaming`` plus it removes any declaration of the renamed symbols. ``coq_expr`` therefore needs to be defined in Coq standard library or in the Coq file specified with the option ``--requiring``. It is not necessary to have entries for the symbols corresponding to the builtins ``"El"`` and ``"Prf"`` declared with the option ``--encoding`` since they are erased automatically. Example: `erasing.lp <https://github.com/Deducteam/lambdapi/blob/master/libraries/erasing.lp>`__.

* ``--use-notations`` instructs Lambdapi to use the usual Coq notations for the symbols corresponding to the builtins ``"eq"``, ``"not"``, ``"and"`` and ``"or"``.

Examples of libraries exported to Coq:
  - In the Lambdapi sources, see how to export the Holide Dedukti library obtained from OpenTheory in `README.md <https://github.com/Deducteam/lambdapi/blob/master/libraries/README.md>`__.
  - See in `hol2dk <https://github.com/Deducteam/hol2dk>`__ how to export the Lambdapi library obtained from HOL-Light.

index
-----

* ``--add`` tells lambdapi to not erase ``~/.LPSearch.db`` before adding new symbols and rules.

* ``--rules <LPSearch.lp>`` tells lambdapi to normalize terms using the rules given in the file ``<LPSearch.lp>`` before indexing. Several files can be specified by using several ``--rules`` options. In these files, symbols must be fully qualified but no ``require`` command is needed. Moreover, the rules do not need to preserve typing. On the other hand, right hand-side of rules must contain implicit arguments.

  For instance, to index the Matita library, you can use the following rules:

::

   rule cic.Term _ $x ↪ $x;
   rule cic.lift _ _ $x ↪ $x;

websearch
---------

* ``--port=<N>`` specifies the port number to use (default is 8080).

lsp
-------

* ``--standard-lsp`` restricts to standard LSP protocol (no extension).

* ``--log-file=<FILE>`` sets the log file for the LSP server. If not given, the file ``/tmp/lambdapi_lsp_log.txt`` is used.

(un)install
-----------

* ``--dry-run`` prints the system commands that should be called instead of running them.

decision-tree
-------------

* ``--ghost`` print the decision tree of a ghost symbol. Ghost symbols are symbols used internally that cannot be used in the concrete syntax.

confluence
----------

* ``--confluence=<CMD>`` checks the confluence of the rewriting system by calling an external prover with the command ``CMD``. The given command receives `HRS`_ formatted text on its standard input, and is expected to output on the first line of its standard output either ``YES``, ``NO`` or ``MAYBE``.  As an example, ``echo MAYBE`` is the simplest possible (valid) confluence checker that can be used.

For now, only the `CSI^ho`_ confluence checker has been tested with Lambdapi. It
can be called using the flag ``--confluence "path/to/csiho.sh --ext trs --stdin"``.

To inspect the ``.trs`` file generated by Lambdapi, one may use the following dummy command: ``--confluence "cat > output.trs; echo MAYBE"``.

termination
-----------

* ``--termination=<CMD>`` checks the termination of the rewriting system by calling an external prover with the command ``CMD``. The given command receives `XTC`_ formatted text on its standard input, and is expected to output on the first line of its standard output either ``YES``, ``NO`` or ``MAYBE``.  ``echo MAYBE`` is the simplest (valid) command for checking termination.

To the best of our knowledge, the only termination checker that is compatible with all the features of Lambdapi is `SizeChangeTool <https://github.com/Deducteam/SizeChangeTool>`__. It can be called using the flag ``--termination "path/to/sct.native --no-color --stdin=xml"``

If no type-level rewriting is used `Wanda <http://wandahot.sourceforge.net/>`_ can also be used. However, it does not directly accept input on its standard input, so it is tricky to have Lambdapi call it directly. Alternatively, one can first generate a ``.xml`` file as described below.

To inspect the ``.xml`` file generated by Lambdapi, one may use the following dummy command:``--termination "cat > output.xml; echo MAYBE"``.

.. _HRS: http://project-coco.uibk.ac.at/problems/hrs.php
.. _CSI^ho: http://cl-informatik.uibk.ac.at/software/csi/ho/
.. _XTC: http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB/raw-file/tip/xml/xtc.xsd
