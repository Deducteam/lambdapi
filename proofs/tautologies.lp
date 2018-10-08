require open proofs.logic
require open proofs.bool

// [∀ a, bool_and a a = a]
theorem and_idempotent : ∀a, P (eq bool (bool_and a a) a)
proof
  intro a
  refine bool_ind (λa, eq bool (bool_and a a) a) ?CT[a] ?CF[a] a
  reflexivity
  reflexivity
qed

// Same with a reduction rule.

rule bool_and &a &a → &a

theorem and_idempotent_rw : ∀a, P (eq bool (bool_and a a) a)
proof
  intro a
  reflexivity
qed
