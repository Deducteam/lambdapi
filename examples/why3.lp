require open proofs.logic
require open proofs.nat
why3init

symbol a : Prop
symbol b : Prop

theorem nat_sym : P(imp ({|and|} a b) a)
proof
    why3 altergo
qed