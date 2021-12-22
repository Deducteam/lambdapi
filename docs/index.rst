.. Lambdapi User Manual documentation master file, created by
   sphinx-quickstart on Tue Jul  7 09:43:57 2020.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Lambdapi User Manual
====================

Lambdapi is a proof assistant for the λΠ-calculus modulo
rewriting. See :doc:`about` for more details.

For installation instructions, see `README
<https://github.com/Deducteam/lambdapi/blob/master/README.md>`__.

Lambdapi files must end with ``.lp``. But Lambdapi can also read `Dedukti <https://deducteam.github.io/>`__
files ending with ``.dk`` and convert them to Lambdapi files.

.. toctree::
   :maxdepth: 1

   about.rst
   getting_started.rst
   options.rst

.. toctree::
   :maxdepth: 2

   ui.rst

.. toctree::
   :maxdepth: 1

   module.rst
   terms.rst
   commands.rst
   tactics.rst
   queries.rst
   dedukti.rst
   latex.rst

For developers
""""""""""""""

`Guidelines for contributing <https://github.com/Deducteam/lambdapi/blob/master/CONTRIBUTING.md>`__

.. toctree::
   :maxdepth: 1

   structure.rst
   implementation.rst
   dtrees.rst
   testing.rst
   profiling.rst

Indices and tables
""""""""""""""""""

* :ref:`genindex`
* :ref:`search`
