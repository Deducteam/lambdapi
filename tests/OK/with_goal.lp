require open tests.OK.Tactic;

injective symbol σ: Prop → Set;
rule π $P ↪ τ (σ $P);

constant symbol ∀[T]: (τ T → Prop) → Prop;
notation ∀ quantifier;
rule π (@∀ $T $P) ↪ Π (x: τ $T), π ($P x);
constant symbol ⇒: Prop → Prop → Prop;
notation ⇒ infix right 7;
builtin "imp" ≔ ⇒;
builtin "all" ≔ ∀;
constant symbol T: Set;
constant symbol P: τ T → Prop;

sequential symbol prove: Prop → Tactic;
rule prove (@∀ $T $P) ↪ #assume "x" (λ (x: τ $T), prove ($P x))
with prove ($P ⇒ $Q) ↪ #assume "h" (λ (h: π $P), prove $Q)
with prove _ ↪ #print "" & #assumption;

symbol test : Π x,  π (P x) → π (P x) ≔
begin
  eval (#with_goal prove);
end;
