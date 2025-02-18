Tacticals
=========

The BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

.. _orelse:

``orelse``
----------

``orelse T1 T2`` applies ``T1``. If ``T1`` succeeds, then ``orelse T1 T2`` stops. Otherwise, ``orelse T1 T2`` applied ``T2``.

.. _repeat:

``repeat``
----------

``repeat T`` applies ``T`` on the first goals as long as possible, unless the number of goals decreases, in which case the tactic stops.

.. _try:

``try``
-------

``try T`` applies ``T``. If ``T`` fails, then ``try T`` leaves the goal unchanged.
