.. Lambdapi User Manual documentation master file, created by
   sphinx-quickstart on Tue Jul  7 09:43:57 2020.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Lambdapi User Manual
====================

Lambdapi is a proof assistant for the λΠ-calculus modulo
rewriting. See :doc:`about` for more details.

Lambdapi files must end with ``.lp``. But Lambdapi can also read
`Dedukti <https://deducteam.github.io/>`__ files ending with ``.dk``
and convert them to Lambdapi files (see :doc:`dedukti`).

`Installation instructions
<https://github.com/Deducteam/lambdapi/blob/master/README.md>`__
- `Frequently Asked Questions
<https://github.com/Deducteam/lambdapi/discussions>`__
- `Issue tracker
<https://github.com/Deducteam/lambdapi/issues>`__

`Learn Lambdapi in 15 minutes <https://raw.githubusercontent.com/Deducteam/lambdapi/master/tests/OK/tutorial.lp>`__

Examples of developments made with Lambdapi:

  - `Some logic definitions <https://github.com/Deducteam/lambdapi-logics>`__
  - `Library on natural numbers, integers and polymorphic lists <https://github.com/Deducteam/lambdapi-stdlib>`__
  - `Example of inductive-recursive type definition <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/indrec.lp>`__
  - `Example of inductive-inductive type definition <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/indind.lp>`__
  - `Test files <https://github.com/Deducteam/lambdapi/tree/master/tests/OK>`__

`Opam repository of Lambdapi libraries <https://github.com/Deducteam/opam-lambdapi-repository>`__

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
   proof.rst
   tactics.rst
   equality.rst
   tacticals.rst
   queries.rst
   query_language.rst
   dedukti.rst
   latex.rst

For developers
""""""""""""""

`Guidelines for contributing <https://github.com/Deducteam/lambdapi/blob/master/CONTRIBUTING.md>`__

.. toctree::
   :maxdepth: 1

   structure.rst
   dtrees.rst
   testing.rst
   profiling.rst

Indices and tables
""""""""""""""""""

* :ref:`genindex`
* :ref:`search`
