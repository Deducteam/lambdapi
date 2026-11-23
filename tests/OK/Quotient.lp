// quotient types

require open tests.OK.Eq;

symbol Rel a ≔ τ a → τ a → Prop;

[a:Set] (r:Rel a) inductive Quot : TYPE ≔ cl:τ a → Quot r;

constant symbol ⫽ : Π a, (τ a → τ a → Prop) → Set; // \sslash
notation ⫽ infix 30;

rule τ (_ ⫽ $R) ↪ Quot $R;

symbol class [a] r ≔ @cl a r;

symbol sound [a] (r:Rel a) x y: π(r x y) → π (class r x = class r y);

symbol lift [a] (r:Rel a) [b] (f:τ a → τ b):
  (Π x₁ x₁', π(r x₁ x₁') → π(f x₁ = f x₁')) → τ(a ⫽ r) → τ b;

rule lift _ $f _ (cl $x) ↪ $f $x;

symbol lift2 [a] (r:Rel a) (hr:Π x, π(r x x)) [b] (f:τ a → τ a → τ b)
  (hf:Π x₁ x₁', π(r x₁ x₁') → Π x₂ x₂', π(r x₂ x₂') → π(f x₁ x₂ = f x₁' x₂')):
  τ(a ⫽ r) → τ(a ⫽ r) → τ b ≔
begin
  assume a r hr b f hf;
  refine λ c d, lift r (λ x, lift r (f x) _ d) _ c
    { assume y y' yy'; apply hf {apply hr} {apply yy'} }
    { assume x x' xx'; set p ≔ λ x y y' yy', hf x x (hr x) y y' yy';
      change π(lift r (f x) (p x) d = lift r (f x') (p x') d);
      set q ≔ λ d, lift r (f x) (p x) d = lift r (f x') (p x') d;
      change π(q d); apply ind_Quot q _ d;
      assume y; simplify; apply hf {apply xx'} {apply hr} }
end;

assert (a:Set) (r:Rel a) (hr:Π x,π(r x x)) b (f:τ a → τ a → τ b)
  (hf:Π x₁ x₁', π(r x₁ x₁') → Π x₂ x₂', π(r x₂ x₂') → π(f x₁ x₂ = f x₁' x₂'))
  (x y:τ a) ⊢ lift2 r hr f hf (class r x) (class r y) ≡ f x y;
