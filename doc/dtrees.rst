Decision trees
==============

The pattern matching algorithm uses decision trees. These decision trees
are attached to symbols and can be inspected for debugging purposes.
To print the decision tree of a symbol ``s`` of a module whose *module path* is
``M`` (see :doc:`Module path <module>`), its decision tree may be printed with

::

   lambdapi decision-tree M.s

The package configuration file of module ``M`` must be above the current working
directory (closer to the root of the file system), or in the same directory.

The decision trees are printed to the standard output in the `dot`_ language. A
dot file ``tree.gv`` can be converted to a png image using
``dot -Tpng tree.gv > tree.png``. The one-liner

.. code:: shell

   lambdapi decision-tree M.s | dot -Tpng | display

displays the decision tree of symbol ``M.s`` (``display`` is part of
`imagemagick`_). For other output formats, see `graphviz documentation`_.

Description of the generated graphs
-----------------------------------

Decision trees are interpreted during evaluation of terms to get the
correct rule to apply. A node is thus an instruction for the evaluation
algorithm. There are labeled nodes, labeled edges and leaves.

* Circle represent *regular* nodes. Let ``n`` be the label of the node, the next
  node is reached by performing an atomic match between the ``n``\ th term of
  the stack and the labels of the edges between the node and its children. Let
  ``t`` be the term taken from the stack and matched against the labels. The
  labels of the edges can be

  * ``s_n``, the atomic match succeeds if ``t`` is the symbol ``s`` applied to
    ``n`` arguments, the ``n`` arguments are put back in the stack;

  * ``λvn``, the atomic match succeeds if ``t`` is an abstraction. the body is
    substituted with (fresh) variable ``vn``. Both the domain of the abstraction
    and the substituted body are put back into the stack;

  * ``Πvn``, the atomic match succeeds if ``t`` is a product. The body is
    substituted with a (fresh) variable ``vn``. Both the domain of the product
    and the substituted body are put back into the stack

  * ``*``, the atomic match succeeds whatever ``t`` is.

* Rectangles represent *storage* nodes. They behave like regular nodes,
  except that the term of the stack is saved for later use.

* Diamonds represent *condition* nodes. The next node is reached by
  performing a condition check on terms that have been saved. If the
  condition is validated, the ``✓``-labeled edge is followed, and the
  ``✗``-labeled one is followed otherwise. The label of the nodes
  indicates the condition, it can be

  * ``n ≡ m`` which succeeds if the ``n``\ th and ``m``\ th saved terms are
    convertible,
  * ``xs ⊆ FV(n)`` which succeeds if the free variables of the ``n``\ th saved
    term is a superset of the free variables ``xs``.

* Triangles represent *stack check* nodes. The next node is the left child if
  the stack of arguments is empty, the right child otherwise. These nodes can
  only appear in trees built for sequential symbols.

**Note for developers:** the decision tree of ghost symbols can be printed as
well using the ``--ghost`` flag. For instance,

::

   lambdapi decision-tree --ghost M.≡

.. _dot: https://www.graphviz.org/doc/info/lang.html
.. _imagemagick: https://imagemagick.org
.. _graphviz documentation: https://graphviz.gitlab.io/_pages/doc/info/output.html
