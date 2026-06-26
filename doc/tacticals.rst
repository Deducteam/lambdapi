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
   builtin "all_hyps" ≔ …; // : (Π p, Prf p → T) → T
   builtin "apply" ≔ …; // : Π [p], Prf p → T
   builtin "assume" ≔ …; // : String → Π [a], (El a → T) → T
   builtin "assumption" ≔ …; // : T
   builtin "apply" ≔ …; // : Π [p], Prf p → T
   builtin "fail" ≔ …; // : T
   builtin "first_hyp" ≔ …; // : (Π p, Prf p → T) → T
   builtin "focus" ≔ …; // : String -> T
   builtin "generalize" ≔ …; // : Π [a], El a → T
   builtin "have" ≔ …; // : String → Prop → T  
   builtin "induction" ≔ …; // : T
   builtin "orelse" ≔ …; // : T → T → T
   builtin "print" ≔ …; // : String → T
   builtin "refine" ≔ …; // : String → T
   builtin "reflexivity" ≔ …; // : T
   builtin "remove" ≔ …; // : Π [a], El a → T
   builtin "repeat" ≔ …; // : T → T
   builtin "rewrite" ≔ …; // : String → String → Π [p], Prf p → T
   builtin "set" ≔ …; // : String → Π [a], El a → T
   builtin "simplify" ≔ …; // : T
   builtin "simplify rule off" ≔ …; // : T
   builtin "solve" ≔ …; // : T
   builtin "symmetry" ≔ …; // : T
   builtin "try" ≔ …; // : T → T
   builtin "why3" ≔ …; // : T

The tactics taking a string as argument need the ``"String"`` :ref:`builtin` to be set. The string argument of ``refine`` is parsed as a term, and thus can contain underscores. If the builtin ``"and"`` is mapped to some symbol, say ``&``, then ``& t u`` is interpreted as follows: the tactic ``t`` is applied and, in case of success, the tactic ``u`` is applied. All other symbols are interpreted by the corresponding tactics.

An example of use is given in `Tactic.lp <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/Tactic.lp>`__:

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
     eval 2 * #rewrite "" "" addnA & #reflexivity
   end;

.. _first_hyp:

``first_hyp``
-------------

``first_hyp`` takes as argument a term of type ``Π p, Prf p → T``. In a context with ``n`` assumptions ``x₁:Prf p₁``, …, ``xₙ:Prf pₙ``, ``first_hyp t``,  applies the tactic ``t pₙ xₙ``. If the goal is solved, then it stops. Otherwise, it tries with the next assumption, and so on, until one succeeds, or fails.

.. _orelse:

``orelse``
----------

``orelse t1 t2`` applies ``t1``. If ``t1`` succeeds, then ``orelse t1 t2`` stops. Otherwise, ``orelse t1 t2`` applies ``t2``.

.. _repeat:

``repeat``
----------

``repeat t`` applies ``t`` on the first goal until the number of goals decreases.

.. _try:

``try``
-------

``try t`` applies ``t``. If ``t`` fails, then ``try t`` leaves the goal unchanged.
