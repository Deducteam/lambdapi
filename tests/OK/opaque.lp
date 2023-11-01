// Classical logic Gödel–Gentzen negative translation 
constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

injective symbol π : Prop → TYPE; // `p
builtin "P" ≔ π;

symbol ⊥: Prop;
symbol a: Prop;

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5; // =>
rule π ($p ⇒ $q) ↪ π $p → π $q;

symbol ¬ p ≔ p ⇒ ⊥; notation ¬ prefix 35;

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix left 6; // \/ or \vee
constant symbol ∨ᵢ₁ [p q] : π p → π (p ∨ q);

symbol πᶜ p ≔ π (¬ ¬ p);

symbol ∨ᶜ p q ≔ (¬ (¬ p)) ∨ (¬ (¬ q)); notation ∨ᶜ infix right 20;

opaque symbol ∨ᶜᵢ₁ [p q] : πᶜ p → πᶜ (p ∨ᶜ q) ≔
begin
    simplify;
    assume p q Hnnp;
    assume Hnnp_or_nnq;
    apply Hnnp_or_nnq;
    apply ∨ᵢ₁;
    refine Hnnp;
end;

opaque πᶜ;
opaque ∨ᶜ;

print πᶜ;
print ∨ᶜ;

print ∨ᶜᵢ₁;

opaque symbol ∨ᶜᵢ₁' [p q] : πᶜ p → πᶜ (p ∨ᶜ q) ≔
begin
    assume p q Hp;
    simplify;
    apply ∨ᶜᵢ₁;
    //apply Hp;
end;
