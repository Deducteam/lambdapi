// dependent pairs

require open tests.OK.Eq;

[a: Set] (p: τ a → Set) inductive DProd : TYPE ≔
  dpair (x: τ a) : τ (p x) → DProd p;

constant symbol dprod [a: Set] : (τ a → Set) → Set;

rule τ (@dprod $a $p) ↪ @DProd $a $p;

symbol proj₁ [a p] (e: @DProd a p) : τ a;

rule proj₁ (dpair $x _) ↪ $x;

symbol proj₂ [a p] (e: @DProd a p) : τ (p (proj₁ e));

rule proj₂ (dpair _ $u) ↪ $u;

opaque symbol η_dprod [a] [p] (e: @DProd a p) :
  π (dpair (proj₁ e) (proj₂ e) = e) ≔
begin assume a p; induction; reflexivity end;

opaque symbol eq_proj₁ [a] [p] (x y: @DProd a p) :
  π (x = y) → π (proj₁ x = proj₁ y) ≔
begin assume a p x y h; refine feq proj₁ h end;

opaque symbol eq_dpair_refl [a] [p] (x: τ a) (u v: τ (p x)) :
  π (u = v) → π (@dpair a p x u = dpair x v) ≔
begin assume a p x u v h; refine feq (dpair x) h end;

symbol transport [a] (p: τ a → Set) [x y: τ a] : π (x = y) → τ (p x) → τ (p y);
rule transport _ (eq_refl _) $u ↪ $u;

symbol eq_dpair [a] [p] (x y: τ a) (u: τ (p x)) (v: τ (p y)) (h: π (x = y)) :
  π (transport p h u = v) → π (@dpair a p x u = dpair y v);
