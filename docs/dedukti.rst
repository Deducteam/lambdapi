Compatibility with Dedukti
==========================

Lambdapi can read `Dedukti <https://deducteam.github.io/>`__ files
with the extension ``.dk``. The Dedukti grammar is given in
`syntax_dedukti.bnf
<https://raw.githubusercontent.com/Deducteam/lambdapi/master/docs/syntax_dedukti.bnf>`__.

Moreover, a Lambdapi file can refer to a symbol declared in a Dedukti file.

In case there are two files ``file.dk`` and ``file.lp``, ``file.lp`` is used.

Finally, Dedukti files can be converted to Lambdapi syntax by using
the ``beautify`` :doc:`command <options>`.
