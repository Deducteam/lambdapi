// Define the CoC encoding
symbol Prop : TYPE;
symbol Type : TYPE;

injective symbol π : Prop → TYPE;
injective symbol ε : Type → TYPE;

symbol dotProp : Type;
rule ε dotProp ↪ Prop;

symbol ∀ₚₚ [x : Prop] : (π x → Prop) → Prop;
symbol ∀ₚₜ [x : Prop] : (π x → Type) → Type;
symbol ∀ₜₚ [x : Type] : (ε x → Prop) → Prop;
symbol ∀ₜₜ [x : Type] : (ε x → Type) → Type;

rule π (∀ₚₚ $f) ↪  Π w, π ($f w)
with ε (∀ₚₜ $f) ↪  Π w, ε ($f w)
with π (∀ₜₚ $f) ↪  Π w, π ($f w)
with ε (∀ₜₜ $f) ↪  Π w, ε ($f w);

symbol ⇒ A B ≔  @∀ₚₚ A (λ _, B);
notation ⇒  infix right 14;

notation ∀ₜₚ quantifier;

// Define the equality in this setting
symbol = [T] (x y : π T) : Prop
≔ `∀ₜₚ P, P y ⇒ P x;
notation = infix 20;

symbol =_refl [T] (x : π T) : π (x = x) ≔ λ P px, px;
symbol =_ind [T] (x y : π T) : π (x = y) → Π P, π (P y) → π (P x)
≔ λ eqxy, eqxy (λ t, t = y) (=_refl y);

builtin "P"     ≔ π;
builtin "Prop"  ≔ Prop;
builtin "T"     ≔ π;
builtin "eq"    ≔ =;
builtin "refl"  ≔ =_refl;
builtin "eqind" ≔ =_ind;

inductive ℕ : TYPE ≔
| zero : ℕ
| s : ℕ → ℕ;

symbol nat : Prop;
rule π nat ↪ ℕ;


symbol rewrite_test (x : ℕ) : π (x = x)
≔ begin

  induction
    { reflexivity }
    { reflexivity }

end;
