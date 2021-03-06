flag "print_domains" on;

symbol R : TYPE;
constant symbol zero : R;
symbol d2_1 : (R → R → R) → (R → R → R);

// The following are equivalent
rule d2_1 (λ _ y, $F[y]) ↪ λ _ _,zero; // warning
rule d2_1 (λ _ y, $_[y]) ↪ λ _ _,zero; // warning
rule d2_1 (λ _ y, _    ) ↪ λ _ _,zero; // no warning

// The following two are currently NOT the same
// (see https://github.com/Deducteam/lambdapi/issues/294)
rule d2_1 (λ x y, $_[y]) ↪ λ _ _,zero; // no warning
rule d2_1 (λ _ y, _    ) ↪ λ _ _,zero; // no warning
// The difference is that in the former variable "x" may appear in the type
// of the "y" variable. That is not the case in the second line.

// New warnings for (unused) bound λ-variables.
symbol fst1 : R → R → R ≔ λ x y , x; // warning since y not bound.
symbol fst2 : R → R → R ≔ λ x _ , x; // no warning
symbol fst3 : R → R → R ≔ λ x _y, x; // no warning either
