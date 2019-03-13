require open proofs.logic
require open proofs.nat

set prover "Alt-Ergo"
set prover_limit 2


theorem test_gamma : ∀ (a : Prop), P a ⇒ P a
proof
    intro a pa
    why3
qed