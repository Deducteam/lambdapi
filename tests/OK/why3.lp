require open tests.OK.logic
require open tests.OK.nat

set prover "Alt-Ergo"
set prover_timeout 2


theorem tautology : Π (a : Prop), P a → P a
proof
    assume a pa
    why3
qed

theorem thm_and1 : Π (a b : Prop), P ({|and|} a b) → P a
proof
    assume a b pab
    why3
qed


theorem thm_and2 : Π (a b : Prop), P ({|and|} a b) → P b
proof
    assume a b pab
    why3
qed

theorem excluded_middle : Π (a : Prop), P (or a (not a))
proof
    assume a
    why3
qed

theorem thm_or1 : Π (a b : Prop), P a → P (or a b)
proof
    assume a b pa
    why3
qed

theorem thm_or2 : Π (a b : Prop), P b → P (or a b)
proof
    assume a b pb
    why3
qed

theorem thm_imp : Π (a b : Prop), P (imp a b) → P a → P b
proof
    assume a b pab pa
    why3
qed
