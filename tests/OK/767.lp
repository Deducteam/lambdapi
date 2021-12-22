constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;
constant symbol B : Set;
type λ (f : _ → _ → τ B) (g : τ B → τ B) b1 b2, f (g b1) (g b2);
