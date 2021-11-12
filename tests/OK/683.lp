symbol Prop : TYPE;
symbol Type : TYPE;

symbol T : Type → TYPE;

symbol prop : Type;
rule T prop ↪ Prop;

symbol ∀ [x : Type] : (T x → Prop) → Prop;
notation ∀ quantifier;

unif_rule Prop ≡ T $t ↪ { $t ≡ prop };

symbol ⊥ : Prop ≔ `∀ C : Prop, C;
