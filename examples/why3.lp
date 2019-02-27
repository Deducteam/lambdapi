require open proofs.logic
require open proofs.nat

set prover altergo
set prover_limit 2

symbol a : Prop

theorem test_gamma : P a ⇒ P a
proof
    intro proof_a
    why3
qed
