require open tests.preuves_Ledein.notation
require open tests.preuves_Ledein.Logic

// Excluded middle
constant symbol excl_mid : ∀ (p : Prop), π (p ∨ (¬ p))




theorem not_elimp : ∀ (A : Prop), π (¬ (¬ A)) ⇒ π A
proof
    assume A nnp
    refine or_elim A (¬ A) A _ _ _
    refine excl_mid A
    assume pa
    refine pa
    assume pna
    apply false_elim
    apply not_elim (¬A) nnp
    apply pna
qed
