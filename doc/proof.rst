Proof mode
==========

The ``symbol`` command allows the user to enter an interactive mode to
solve typing goals of the form ``x₁:A₁, …, xₙ:Aₙ ⊢ ?M : U`` (find a
term of a given type materialized by a metavariable ``?M``) and
unification goals of the form ``x₁:A₁, …, xₙ:Aₙ ⊢ U ≡ V`` (prove that
two terms are equivalent modulo the user-defined rewriting rules).

The following tactics help users to refine typing goals and transform
unification goals step by step. A tactic application may generate new
goals/metavariables.

Except for the ``solve`` tactic which applies to all the unification
goals at once, all the other tactics applies to the first goal only,
which is called the *focused* goal, and this focused goal must be a
typing goal.

The proof is complete only when all generated goals have been solved.

Proof scripts must be structured. The general rule is: when a tactic
generates several subgoals, the proof of each subgoal must be enclosed
between curly brackets:

::
   
   opaque symbol ≤0 [x] : π(x ≤ 0 ⇒ x = 0) ≔
   begin
     have l : Π x y, π(x ≤ y ⇒ y = 0 ⇒ x = 0)
     { // subproof of l
       refine ind_≤ _ _ _
       { /* case 0 */ reflexivity }
       { /* case s */ assume x y xy h a; apply ⊥ₑ; apply s≠0 _ a }
     };
     assume x h; apply l _ _ h _; reflexivity
   end;

Reminder: the BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

.. _begin:

``begin``
---------

Start a proof.

.. _end:

``end``
-------

Exit the proof mode when all goals have been solved. It then adds in
the environment the symbol declaration or definition the proof is
about.

.. _abort:

``abort``
---------

Exit the proof mode without changing the environment.

.. _admitted:

``admitted``
------------

Add axioms in the environment to solve the remaining goals and exit of
the proof mode.
