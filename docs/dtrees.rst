Decision trees
==============

The pattern matching algorithm uses decision trees. These decision trees
are attached to symbols and can be inspected, mainly for debugging
purposes. To print the decision of a symbol ``s`` of a module ``M``, the
following command may be used if module ``M`` is in a package (the
``lambdapi.pkg`` file) placed *above* the current working directory

::

   lambdapi decision-tree M.s

To print the decision tree of a symbol whose package is below the
current working directory, the option ``--map-dir`` may be used,

::

   lambdapi decision-tree --map-dir=M:dirM M.s

The decision trees are printed to the standard output in the `dot`_ language. A
dot file ``tree.gv`` can be converted to a png image using
``dot -Tpng tree.gv > tree.png``. The one-liner

.. code:: shell

   lambdapi decision-tree M.s | dot -Tpng | display

displays the decision tree of symbol ``M.s``. For other output formats,
see `graphviz documentation`_.

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

**Note for developers:** ghost symbols can be printed as well, for
instance

::

   lambdapi decision-tree M.#equiv

.. _dot: https://www.graphviz.org/doc/info/lang.html
.. _graphviz documentation: https://graphviz.gitlab.io/_pages/doc/info/output.html
