Compatibility with Dedukti
==========================

Lambdapi can read `Dedukti <https://raw.githubusercontent.com/Deducteam/Dedukti/master/syntax.bnf>`__ files
with the extension ``.dk``.

Moreover, a Lambdapi file can refer to a symbol declared in a Dedukti file.

In case there are two files ``file.dk`` and ``file.lp``, ``file.lp`` is used.

Finally, Dedukti files can be converted to Lambdapi syntax by using
the ``beautify`` :doc:`command <options>`.
