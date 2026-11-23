// disjoint sum

require open tests.OK.FOL tests.OK.Eq;

(a: Set) (b: Set) inductive Sum: TYPE ≔
| inl: τ a → Sum a b
| inr: τ b → Sum a b;

constant symbol sum : Set → Set → Set;

rule τ (sum $a $b) ↪ Sum $a $b;

// Universal property: a map out of a sum is given by case analysis

symbol sum_case [a b c] : τ (sum a b) → (τ a → τ c) → (τ b → τ c) → τ c;

rule sum_case (inl $x) $f _ ↪ $f $x
with sum_case (inr $y) _ $g ↪ $g $y;

opaque symbol sum_case_uniq [a b c] (h: τ (sum a b) → τ c) (s: τ (sum a b)) :
  π (sum_case s (λ x, h (inl x)) (λ y, h (inr y)) = h s) ≔
begin
  assume a b c h; induction { reflexivity } { reflexivity }
end;

opaque symbol η_sum [a b] (s: τ (sum a b)) :
  π (sum_case s (λ x, inl x) (λ y, inr y) = s) ≔
begin
  assume a b; induction { reflexivity } { reflexivity }
end;

// non confusion of constructors

symbol is_inl [a b] : τ (sum a b) → Prop;

rule is_inl (inl _) ↪ ⊤
with is_inl (inr _) ↪ ⊥;

opaque symbol inr≠inl [a b] (x: τ a) (y: τ b) : π (@inr a b y ≠ inl x) ≔
begin assume a b x y h; refine ind_eq h (λ s, is_inl s) ⊤ᵢ end;

opaque symbol inl≠inr [a b] (x: τ a) (y: τ b) : π (@inl a b x ≠ inr y) ≔
begin assume a b x y h; apply inr≠inl x y; symmetry; apply h end;

symbol outl [a b] (s: τ (sum a b)) : τ a ≔ sum_case s (λ x, x) (λ _, el a);
symbol outr [a b] (s: τ (sum a b)) : τ b ≔ sum_case s (λ _, el b) (λ y, y);

opaque symbol inl_inj [a b] (x x': τ a) : π (@inl a b x = inl x') → π (x = x') ≔
begin assume a b x x' h; refine feq (λ s, @outl a b s) h end;

opaque symbol inr_inj [a b] (y y': τ b) : π (@inr a b y = inr y') → π (y = y') ≔
begin assume a b y y' h; refine feq (λ s, @outr a b s) h end;

// induction principle with equalities

opaque symbol case_Sum [a b] (s: τ (sum a b)) :
  π ((`∃ x, s = inl x) ∨ (`∃ y, s = inr y)) ≔
begin
  assume a b; induction
  { assume x; apply ∨ᵢ₁; apply ∃ᵢ x; reflexivity }
  { assume y; apply ∨ᵢ₂; apply ∃ᵢ y; reflexivity }
end;

opaque symbol ind_Sum_eq [a b] (p: τ (sum a b) → Prop) (s: τ (sum a b)) :
  (Π x, π (s = inl x) → π (p s)) → (Π y, π (s = inr y) → π (p s)) → π (p s) ≔
begin
  assume a b p s hl hr; refine ∨ₑ (case_Sum s) (λ h, ∃ₑ h hl) (λ h, ∃ₑ h hr)
end;

symbol map_sum [a b c d] (f: τ a → τ c) (g: τ b → τ d) (s: τ (sum a b))
  : τ (sum c d) ≔ sum_case s (λ x, inl (f x)) (λ y, inr (g y));

opaque symbol map_sum_id [a b] (s: τ (sum a b)) :
  π (map_sum (λ u, u) (λ v, v) s = s) ≔
begin assume a b s; refine η_sum s end;

opaque symbol map_sum_comp [a b c d e f]
  (g: τ c → τ e) (g': τ d → τ f) (h: τ a → τ c) (h': τ b → τ d) (s: τ (sum a b)) :
  π (map_sum g g' (map_sum h h' s) = map_sum (λ u, g (h u)) (λ v, g' (h' v)) s) ≔
begin
  assume a b c d e f g g' h h';
  induction { reflexivity } { reflexivity }
end;

symbol swap_sum [a b] (s: τ (sum a b)) : τ (sum b a) ≔
  sum_case s (λ x, inr x) (λ y, inl y);

opaque symbol swap_sum_invol [a b] (s: τ (sum a b)) :
  π (swap_sum (swap_sum s) = s) ≔
begin
  assume a b; induction { reflexivity } { reflexivity }
end;

// currying

symbol sum_curry₁ [a b c] (h: τ (sum a b) → τ c) (x: τ a) : τ c ≔ h (inl x);
symbol sum_curry₂ [a b c] (h: τ (sum a b) → τ c) (y: τ b) : τ c ≔ h (inr y);

symbol sum_uncurry [a b c] (f: τ a → τ c) (g: τ b → τ c) (s: τ (sum a b)) : τ c ≔
  sum_case s f g;

opaque symbol sum_uncurry_curry [a b c] (h: τ (sum a b) → τ c) (s: τ (sum a b)) :
  π (sum_uncurry (sum_curry₁ h) (sum_curry₂ h) s = h s) ≔
begin
  assume a b c h; induction { reflexivity } { reflexivity }
end;

opaque symbol sum_curry_uncurry₁ [a b c] (f: τ a → τ c) (g: τ b → τ c) (x: τ a) :
  π (sum_curry₁ (sum_uncurry f g) x = f x) ≔
begin reflexivity end;

opaque symbol sum_curry_uncurry₂ [a b c] (f: τ a → τ c) (g: τ b → τ c) (y: τ b) :
  π (sum_curry₂ (sum_uncurry f g) y = g y) ≔
begin reflexivity end;

// Relation between the product and the coproduct

require open tests.OK.Prod;

symbol dist_× [a b c] (x: τ (a × sum b c)) : τ (sum (a × b) (a × c)) ≔
  sum_case (x ₂) (λ y, inl ((x ₁) ‚ y)) (λ z, inr ((x ₁) ‚ z));

symbol undist_× [a b c] (s: τ (sum (a × b) (a × c))) : τ (a × sum b c) ≔
  sum_case s (λ u, (u ₁) ‚ inl (u ₂)) (λ v, (v ₁) ‚ inr (v ₂));

opaque symbol undist_dist_‚ [a b c] (u: τ a) (s: τ (sum b c)) :
  π (undist_× (dist_× (u ‚ s)) = u ‚ s) ≔
begin
  assume a b c u; induction { reflexivity } { reflexivity }
end;

opaque symbol undist_dist_× [a b c] (x: τ (a × sum b c)) :
  π (undist_× (dist_× x) = x) ≔
begin
  assume a b c x; rewrite prodExt x; refine undist_dist_‚ (x ₁) (x ₂)
end;

opaque symbol dist_undist_× [a b c] (s: τ (sum (a × b) (a × c))) :
  π (dist_× (undist_× s) = s) ≔
begin
  assume a b c; induction
  { assume u; symmetry; refine feq inl (prodExt u) }
  { assume v; symmetry; refine feq inr (prodExt v) }
end;
