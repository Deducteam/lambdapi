Tacticals
=========

The BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

.. _eval:

``eval``
--------

``eval`` takes as argument a term which, after normalization, can be interpreted as a tactic expression using the following builtins:

::

   builtin "admit" ≔ …; // : T
   builtin "and" ≔ …; // : T → T → T (stands for ";")
   builtin "apply" ≔ …; // : Π [a], P a → T  
   builtin "fail" ≔ …; // : T
   builtin "induction" ≔ …; // : T
   builtin "orelse" ≔ …; // : T → T → T
   builtin "refine" ≔ …; // : Π [a], P a → T  
   builtin "reflexivity" ≔ …; // : T
   builtin "repeat" ≔ …; // : T → T
   builtin "rewrite" ≔ …; // : Π [a], P a → T  
   builtin "simplify" ≔ …; // : T
   builtin "solve" ≔ …; // : T
   builtin "symmetry" ≔ …; // : T
   builtin "try" ≔ …; // : T → T
   builtin "why3" ≔ …; // : T

An example of use is given in `tactic.lp <https://github.com/Deducteam/lambdapi/blob/tac/tests/OK/tactic.lp>`__:

::

   symbol do_nothing ≔ #try #fail;

   require open tests.OK.Nat;

   symbol * : ℕ → Tactic → Tactic;
   notation * infix 20;

   rule 0 * _ ↪ do_nothing
   with $n +1 * $t ↪ $t & ($n * $t);

   require open tests.OK.Eq;

   symbol lemma x y z t : π (((x + y) + z) + t = x + (y + (z + t))) ≔
   begin
     assume x y z t;
     eval 2 * #rewrite addnA & #reflexivity
   end;

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
