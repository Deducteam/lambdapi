require open proofs.logic
require open proofs.nat

set prover_limit 2

symbol a : Prop
symbol b : Prop

theorem nat_sym : P(imp ({|and|} a b) a)
proof
    why3 altergo
qed