Compatibility with Dedukti
==========================

Lambdapi can also read most of
`Dedukti <https://deducteam.github.io/>`__ files (extension ``.dk``). The
Dedukti grammar currently supported by Lambdapi can be seen in
`syntax_dedukti.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/docs/syntax_dedukti.bnf>`__.
It should be extended whenever the syntax of Dedukti is extended.

For instance, Lambdapi is able to type-check all the generated
libraries that were aimed at Dedukti (with minor
modifications). Translation scripts are provided in the ``libraries``
folder.

Files can be converted from the Dedukti syntax to the Lambdapi syntax
using the ``--beautify`` command line flag (see the related section).

Note that files in the Dedukti syntax are interoperable with files in
the Lambdapi syntax. The correct parser is selected according to the
extension of the files (``.dk`` for Dedukti files, and ``.lp`` for
Lambdapi files). As a consequence, there cannot be in the same package
two files ``file.dk`` and ``file.lp``.
