// Cartesian product

require open tests.OK.Eq;

(a b:Set) inductive Prod:TYPE ≔ ‚ : τ a → τ b → Prod a b;

notation ‚ infix right 30;

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

rule τ ($a × $b) ↪ Prod $a $b;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x ‚ y ‚ z : τ(a × b × c);
assert x y z ⊢ x ‚ y ‚ z ≡ x ‚ (y ‚ z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x ‚ _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ ‚ $x)₂ ↪ $x;

opaque symbol eq_₁ [a b] (x y: τ (a × b)) : π (x = y) → π ((x ₁) = (y ₁)) ≔
begin assume a b x y h; refine feq (λ z, z ₁) h end;

opaque symbol eq_₂ [a b] (x y: τ (a × b)) : π (x = y) → π ((x ₂) = (y ₂)) ≔
begin assume a b x y h; refine feq (λ z, z ₂) h end;

opaque symbol ‚_inj₁ [a b] (x x': τ a) (y y': τ b) :
  π (x ‚ y = x' ‚ y') → π (x = x') ≔
begin assume a b x x' y y' h; refine eq_₁ (x ‚ y) (x' ‚ y') h end;

opaque symbol ‚_inj₂ [a b] (x x': τ a) (y y': τ b) :
  π (x ‚ y = x' ‚ y') → π (y = y') ≔
begin assume a b x x' y y' h; refine eq_₂ (x ‚ y) (x' ‚ y') h end;

symbol map_× [a b c d] (f: τ a → τ c) (g: τ b → τ d) (x: τ (a × b)) : τ (c × d) ≔
  f (x ₁) ‚ g (x ₂);

opaque symbol map_×_comp [a b c d e f]
  (g: τ c → τ e) (g': τ d → τ f) (h: τ a → τ c) (h': τ b → τ d) (x: τ (a × b)) :
  π (map_× g g' (map_× h h' x) = map_× (λ u, g (h u)) (λ v, g' (h' v)) x) ≔
begin reflexivity end;

symbol swap_× [a b] (x: τ (a × b)) : τ (b × a) ≔ (x ₂) ‚ (x ₁);

symbol pairing [a b c] (f: τ c → τ a) (g: τ c → τ b) : τ c → τ (a × b) ≔
  λ z, f z ‚ g z;

opaque symbol ₁_pairing [a b c] (f: τ c → τ a) (g: τ c → τ b) (z: τ c) :
  π ((pairing f g z ₁) = f z) ≔
begin reflexivity end;

opaque symbol ₂_pairing [a b c] (f: τ c → τ a) (g: τ c → τ b) (z: τ c) :
  π ((pairing f g z ₂) = g z) ≔
begin reflexivity end;

symbol prodExt [a b] (x: τ (a × b)) : π (x = (x ₁) ‚ (x ₂)) ≔
begin
  assume a b; refine ind_Prod (λ x, x = (x ₁) ‚ (x ₂)) _; reflexivity
end;

opaque symbol eq_pair [a b] (x y: τ (a × b)) :
  π ((x ₁) = (y ₁)) → π ((x ₂) = (y ₂)) → π (x = y) ≔
begin
  assume a b x y h1 h2;
  rewrite (prodExt x); rewrite (prodExt y);
  refine feq2 (λ u v, u ‚ v) h1 h2
end;

opaque symbol eq_×_iff [a b] (x y: τ (a × b)) :
  π (x = y ⇔ (x ₁) = (y ₁) ∧ (x ₂) = (y ₂)) ≔
begin
  assume a b x y; apply ∧ᵢ
    { assume h; apply ∧ᵢ { refine eq_₁ x y h } { refine eq_₂ x y h } }
    { assume h; refine eq_pair x y (∧ₑ₁ h) (∧ₑ₂ h) }
end;

opaque symbol map_×_id [a b] (x: τ (a × b)) : π (map_× (λ u, u) (λ v, v) x = x) ≔
begin assume a b x; symmetry; refine prodExt x end;

opaque symbol swap_×_invol [a b] (x: τ (a × b)) : π (swap_× (swap_× x) = x) ≔
begin assume a b x; symmetry; refine prodExt x end;

opaque symbol pairing_uniq [a b c] (h: τ c → τ (a × b)) (z: τ c) :
  π (pairing (λ u, h u ₁) (λ u, h u ₂) z = h z) ≔
begin assume a b c h z; symmetry; refine prodExt (h z) end;
