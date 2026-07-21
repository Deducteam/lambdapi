// issue #700

// Define the CoC encoding
symbol Type : TYPE;
symbol Kind : TYPE;

injective symbol π : Type → TYPE;
injective symbol ε : Kind → TYPE;

symbol dotType : Kind;
rule ε dotType ↪ Type;

symbol ∀ₜₜ [x : Type] : (π x → Type) → Type;
symbol ∀ₜₖ [x : Type] : (π x → Kind) → Kind;
symbol ∀ₖₜ [x : Kind] : (ε x → Type) → Type;
symbol ∀ₖₖ [x : Kind] : (ε x → Kind) → Kind;

rule π (∀ₜₜ $f) ↪  Π w, π ($f w)
with ε (∀ₜₖ $f) ↪  Π w, ε ($f w)
with π (∀ₖₜ $f) ↪  Π w, π ($f w)
with ε (∀ₖₖ $f) ↪  Π w, ε ($f w);

symbol ⇒ A B ≔  @∀ₜₜ A (λ _, B);
notation ⇒ infix right 14;

notation ∀ₖₜ quantifier;

// Define the equality in this setting
symbol = [T] (x y : π T) : Type
// Works if next line is commented
≔ `∀ₖₜ P, P y ⇒ P x
;
notation = infix 20;

// If equality is defined, then we can uncomment the following definition lines
symbol =_refl [T] (x : π T) : π (x = x)
// ≔ λ P px, px
;
symbol =_ind [T] (x y : π T) : π (x = y) → Π P, π (P y) → π (P x)
// ≔ λ eqxy, eqxy (λ t, t = y) (=_refl y)
;

builtin "Prop" ≔ Type;
builtin "Prf"     ≔ π;
builtin "Set" ≔ Type;
builtin "El"     ≔ π;
builtin "eq"    ≔ =;
builtin "refl"  ≔ =_refl;
builtin "eqind" ≔ =_ind;

symbol rewrite_test1 T (x y : π T) (f : π T → Type) : π (x = y ⇒ f x ⇒ f y)
≔ begin
  assume T x y f eqxy;
  have e : π (x = y) {refine eqxy};
  rewrite e;
  assume fy; apply fy
end;

symbol 𝔹 : TYPE;
symbol true : 𝔹;
symbol false : 𝔹;

symbol bool : Type;
rule π bool ↪ 𝔹;

symbol not : 𝔹 → 𝔹;
rule not false ↪ true
with not true ↪ false;

symbol reflexivity_test2 : π (not (not true) = true) ≔
begin
  reflexivity
end;

symbol rewrite_test3 T (x : π T) (f g : π T → π T) (p : π T → Type):
  π ((`∀ₜₜ y, f y = g y) ⇒ p (f x) ⇒ p (g x))
≔ begin
  assume T x f g p e;
  rewrite e;
  refine (λ u, u)
end;
