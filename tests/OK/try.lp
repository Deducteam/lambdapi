
// Type of data type codes and their interpretation as types.

constant symbol U : TYPE;

injective symbol T : U → TYPE;

constant symbol Prop : TYPE;

symbol P : Prop → TYPE;

symbol o: U;
rule T o ↪ Prop;

constant symbol = [a] : T a → T a → Prop;

notation = infix 0.1;

constant symbol refl a (x:T a) : P (x = x);

constant symbol eqind a (x y:T a) : P (x = y) → Π p, P (p y) → P (p x);

builtin "P"     ≔ P;
builtin "T"     ≔ T;
builtin "eq"    ≔ =;
builtin "eqind" ≔ eqind;
builtin "refl"  ≔ refl;


private symbol a: Prop;
private symbol b: Prop;

constant symbol ⊤: Prop;
constant symbol ⊥: Prop;

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix left 7; // /\ or \wedge

constant symbol ∧ᵢ [p q] : P p → P q → P (p ∧ q);
symbol ∧ₑ₁ [p q] : P (p ∧ q) → P p;
symbol ∧ₑ₂ [p q] : P (p ∧ q) → P q;

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix right 6; // \/ or \vee

constant symbol ∨ᵢ₁ [p q] : P p → P (p ∨ q);
constant symbol ∨ᵢ₂ [p q] : P q → P (p ∨ q);
symbol ∨ₑ [p q r] : P (p ∨ q) → (P p → P r) → (P q → P r) → P r;

symbol ¬: Prop → Prop; notation ¬ prefix 2;

symbol eq_simp [a] (x:T a) : P ((x = x) = ⊤);
symbol eq_simp_neg_l x : P ((¬ x = x) = ⊥);
symbol eq_simp_refl_r x : P ((¬ x = x) = ⊥);
symbol eq_simp_2 x : P ((⊥ = x) = ¬ x);

opaque symbol test1 (x : Prop) : P ((¬ x = x) = ⊥)
≔ begin
  assume x;
  try rewrite eq_simp x;  // (fail)
  try rewrite eq_simp_neg_l x;
  try rewrite eq_simp_refl_r x; // (fail)
  try rewrite eq_simp_2 x; // (fail)
  reflexivity
end;

symbol or_simplify_idem x : P ((x ∨ x) = x);
symbol or_simplify_true_r x : P ((x ∨ ⊤) = ⊤);
symbol or_simplify_true_l x : P ((⊤ ∨ x) = ⊤);

opaque symbol test2 (a b c d : Prop) : P (a ∨ ⊤ ∨ c ∨ ⊤ ∨ d ∨ d = ⊤)
≔ begin
  assume a b c d;
  rewrite (or_simplify_idem d);
  try rewrite or_simplify_true_r; // (fail)
  rewrite or_simplify_true_l;
  rewrite or_simplify_true_r;
  reflexivity
end;
