Compatibility with Dedukti
==========================

Lambdapi can read `Dedukti
<https://raw.githubusercontent.com/Deducteam/Dedukti/master/syntax.bnf>`__
files with the extension ``.dk``, and translate Lambdapi files to
Dedukti files, and vice versa, by using the ``export`` :doc:`command
<options>`.

Moreover, a Lambdapi file can refer to a symbol declared in a Dedukti file.

In case there are two files ``file.dk`` and ``file.lp``, ``file.lp`` is used.

**Remarks on the export to Dedukti:**

When a ``lp`` identifier or module/file name is not a valid ``dk``
identifier or module/file name (the ``lp`` and ``dk`` formats do not
accept the same class of identifiers and module/file names), we try to
rename them instead of failing:

- ``lp`` identifiers that are not valid ``dk`` identifiers or that are
  ``dk`` keywords are enclosed between ``{|`` and ``|}``.

- In module names, dots are replaced by underscores and, if a ``lp``
  file requires the module ``mylib.logic.untyped.fol``, its
  translation will require the file
  ``mylib_logic_untyped_fol.dk``. Therefore, in a package whose
  ``root_path`` is ``mylib.logic``, the file ``untyped/fol.lp`` is
  translated into ``mylib_logic_untyped_fol.dk``.
