Compatibility with Dedukti
==========================

One of the aims of Lambdapi is to remain compatible with
`Dedukti <https://deducteam.github.io/>`__. Currently, a second parser
is included in Lambdapi in order to support the legacy syntax of
Dedukti. The grammar supported by that parser can be seen in
:download:`syntax_dedukti.bnf`.
It should be extended whenever the syntax of Dedukti is
extended, but such changes should be discouraged.

Note that files in the legacy (Dedukti) syntax are interoperable with
files in the Lambdapi syntax. The correct parser is selected according
to the extension of files. The extension ``.dk`` is preserved for legacy
files, and the extension ``.lp`` is used for files in the Lambdapi
syntax.

Although both formats are compatible, many features of Lambdapi cannot
be used from the legacy syntax. As a consequence, the use of the legacy
syntax is also discouraged. Files can be converted from the legacy
syntax to Lambdapi syntax using the ``--beautify`` command line flag
(see the related section).

Note that Lambdapi is able to type-check all the generated libraries
that were aimed at Dedukti (with minor modifications). Translation
scripts are provided in the ``libraries`` folder.
