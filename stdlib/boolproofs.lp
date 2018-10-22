require open stdlib.logic
require open stdlib.bool

// ----------------------------------------------------------------------------
// ----------------------- Proofs about the boolean NOT -----------------------
// ----------------------------------------------------------------------------

// Proof that the two definitions of not are equivalent
theorem bool_not_bool_not_2_equiv : ∀b, P (eq bool (bool_not b) (bool_not_2 b))
proof
    intro b
    refine ((bool_ind (λ(bx:B), eq bool (bool_not bx) (bool_not_2 bx)) // FIXME : infer predicate
                      (refl bool false) 
                      (refl bool true)) b) 
qed

// I obviously prefer the first definition, which only forces us to believe 
// in the two induction principles (on Prop and U), rather than relying on 
// additional rewriting rules that can lead to an inconsistent system, and 
// which therefore needs some external analysis (for termination and confluence).

// ----------------------------------------------------------------------------
// ----------------------- Proofs about the boolean OR ------------------------
// ----------------------------------------------------------------------------

// Proof that the two definitions of the boolean or are equivalent
theorem bool_or_bool_or_2_equiv : ∀b1 b2, P (eq bool (bool_or b1 b2) (bool_or_2 b1 b2))
proof
    intro b1 b2
    refine ((bool_ind (λ(b1x:B), eq bool (bool_or b1x b2) (bool_or_2 b1x b2)) // FIXME : infer predicate
                      (refl bool true) 
                      (refl bool b2)) b1) 
qed

theorem bool_or_right_true : ∀b, P(eq bool (bool_or b true) true)
proof
    intro b
    refine  ((bool_ind (λ(bx:B), eq bool (bool_or bx true) true) // FIXME : infer predicate
                       (refl bool true) 
                       (refl bool true)) b)
qed

theorem bool_or_right_false : ∀b, P(eq bool (bool_or b false) b)
proof
    intro b
    refine  ((bool_ind (λ(bx:B), eq bool (bool_or bx false) bx) // FIXME : infer predicate
                       (refl bool true) 
                       (refl bool false)) b) 
qed

// ----------------------------------------------------------------------------
// ----------------------- Proofs about the boolean AND -----------------------
// ----------------------------------------------------------------------------

// Proof that the two definitions of the boolean and are equivalent
theorem bool_and_bool_and_2_equiv : ∀b1 b2, P (eq bool (bool_and b1 b2) (bool_and_2 b1 b2))
proof
    intro b1 b2
    refine  ((bool_ind (λ(b1x:B), eq bool (bool_and b1x b2) (bool_and_2 b1x b2)) // FIXME : infer predicate
                       (refl bool b2) 
                       (refl bool false)) b1) 
qed

theorem bool_and_right_true : ∀b, P(eq bool (bool_and b true) b)
proof
    intro b
    refine  ((bool_ind (λ(bx:B), eq bool (bool_and bx true) bx) // FIXME : infer predicate
                       (refl bool true) 
                       (refl bool false)) b) 
qed

theorem bool_and_right_false : ∀b, P(eq bool (bool_and b false) false)
proof
    intro b
    refine  ((bool_ind (λ(bx:B), eq bool (bool_and bx false) false) // FIXME : infer predicate
                       (refl bool false) 
                       (refl bool false)) b) 
qed

// ----------------------------------------------------------------------------
// ----------------------- Proofs about the boolean IMPL ----------------------
// ----------------------------------------------------------------------------

// Proof that the two definitions of the boolean impl are equivalent
theorem bool_impl_bool_impl_2_equiv : ∀b1 b2, P (eq bool (bool_impl b1 b2) (bool_impl_2 b1 b2))
proof
    intro b1 b2
    // here we gain by having used the versions by rewriting in the def of bool_impl
    refine  ((bool_ind (λ(b2x:B), eq bool (bool_impl b1 b2x) (bool_impl_2 b1 b2x)) // FIXME : infer predicate
                       (refl bool true) 
                       (refl bool (bool_not_2 b1))) b2) 
qed

theorem bool_impl_right_true : ∀b, P(eq bool (bool_impl b true) true)
proof
    intro b
    refine  ((bool_ind (λ(bx:B), eq bool (bool_impl bx true) true) // FIXME : infer predicate
                       (refl bool true) 
                       (refl bool true)) b) 
qed

theorem bool_impl_right_false : ∀b, P(eq bool (bool_impl b false) (bool_not b))
proof
    intro b
    refine  ((bool_ind (λ(bx:B), eq bool (bool_impl bx false) (bool_not bx)) // FIXME : infer predicate
                       (refl bool false) 
                       (refl bool true)) b) 
qed
