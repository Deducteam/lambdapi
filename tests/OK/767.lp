constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;
constant symbol B : Set;
type λ (f : _ → τ B) (b: τ B), f b;
// type λ (f : _ → _ → τ B) (g : τ B → τ B) b1 b2, f (g b1) (g b2);
// The command above fails because the instantiation of the second placeholder
// triggers a unification problem τ B == ?1[g b1], which fails because `g b1`
// is not a variable.
// "arguments are not distinct variables: g b1"
// It worked before this PR because the arrow notation would specify that the
// second meta-variable cannot depend on the first argument.
