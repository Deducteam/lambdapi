require open proofs.logic
require open proofs.bool
require open proofs.nat

theorem z_neutral : ∀n, P(eq nat (add n z) n)
proof
  assert P(eq nat (add z z) z) as H
  reflexivity
  refine nat_ind (λ n,eq nat (add n z) n) H _
  intro n p
  simpl
  reflexivity
qed