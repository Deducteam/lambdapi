require open tests.OK.logic
require open tests.OK.bool

// [Π a, bool_and a a = a]
theorem and_idempotent : Πa, P (eq bool (bool_and a a) a)
proof
  assume a
  refine bool_ind (λa, eq bool (bool_and a a) a) ?CT[a] ?CF[a] a
  reflexivity
  reflexivity
qed

// Same with a reduction rule.

rule bool_and $a $a ↪ $a

theorem and_idempotent_rw : Πa, P (eq bool (bool_and a a) a)
proof
  assume a
  reflexivity
qed
