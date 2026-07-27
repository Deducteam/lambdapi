symbol Prop : TYPE;
symbol Set: TYPE;
injective symbol π: Prop → TYPE;
injective symbol τ: Set → TYPE;

constant symbol ∃ [a] : (τ a → Prop) → Prop;
notation ∃ quantifier;
constant symbol ∃ᵢ [a p] (x:τ a) : π (p x) → π (∃ p);

symbol T: Set;
constant symbol P: τ T → Prop;


symbol test a: π (P a) → π (`∃ x, P x) ≔
begin
  assume a h;
  apply ∃ᵢ {} {};
  focus 2;
  assumption
end;

symbol test2 a: (Π x, π (P x)) → π (P a) ≔
begin
  assume a h;
  assumption;
end;
