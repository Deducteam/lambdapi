symbol Prop: TYPE;
symbol π: Prop → TYPE;
symbol Set: TYPE;
constant symbol τ: Set → TYPE;
builtin "T" ≔ τ;
builtin "P" ≔ π;

symbol = [a:Set] : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl [a:Set] (x:τ a) : π (x = x);
constant symbol ind_eq [a:Set] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

injective symbol σℙ: Set → Set;
symbol σBOOL: Set;
symbol τℙ (T:Set) ≔ τ (σℙ T);


constant symbol ∀ [a] : (τ a → Prop) → Prop;

notation ∀ quantifier;

rule π (∀ $f) ↪ Π x, π ($f x);
symbol ∈ [T:Set] : τ T → τℙ T → Prop;
notation ∈ infix 10;

symbol T: Set;
symbol S1: τℙ T;
symbol S2: τℙ T;
symbol h1: π (S1 = S2);

symbol h2: π (`∀ x, x ∈ S1);

symbol ok: π (`∀ x, x ∈ S2) ≔
begin
  assume x;
  rewrite left h1;
  refine (h2 x);
end;

symbol bug: π (`∀ x, x ∈ S2) ≔
begin
  rewrite left h1;
  refine h2;
end;
