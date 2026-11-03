// subset types

require open tests.OK.FOL tests.OK.Eq;

[a: Set] (p: τ a → Prop) inductive Subset : TYPE ≔
  mk (x: τ a) : π (p x) → Subset p;

symbol elt [a] [p:τ a → Prop] (e: Subset p) : τ a;

rule elt (mk $x _) ↪ $x;

symbol prf [a] [p:τ a → Prop] (e: Subset p) : π (p (elt e));

rule prf (mk _ $h) ↪ $h;

opaque symbol Subset_∃ [a] [p:τ a → Prop] (e: Subset p) : π (`∃ x, p x) ≔
begin assume a p e; refine ∃ᵢ (elt e) (prf e) end;

/* The `subset` Set-constructor requires an existential proof: this is needed
   to be consistent with the axiom `el` of Set.lp stating that every set is
   non-empty. */

constant symbol subset [a] (p: τ a → Prop) : π (`∃ x, p x) → Set;

rule τ (subset $p _) ↪ Subset $p;

opaque symbol η_subset [a] [p:τ a → Prop] [h] (e: τ (subset p h)) :
  π (mk (elt e) (prf e) = e) ≔
begin assume a p h; induction; reflexivity end;

opaque symbol eq_elt [a] [p:τ a → Prop] [h] (x y: τ (subset p h)) :
  π (x = y) → π (elt x = elt y) ≔
begin assume a p h x y e; refine feq elt e end;

opaque symbol mk_inj [a] [p:τ a → Prop] [h] x y (hx: π (p x)) (hy: π (p y)) :
  π (= [subset p h] (mk x hx) (mk y hy)) → π (x = y) ≔
begin assume a p h x y hx hy e; refine @eq_elt a p h (mk x hx) (mk y hy) e end;
