constant symbol Set : TYPE;
injective symbol τ : Set → TYPE; // `t or \tau
builtin "T" ≔ τ;
constant symbol ↦ : Set → Set → Set; // \mapsto
notation ↦ infix right 20;
rule τ($a ↦ $b) ↪ τ $a → τ $b;

constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE; // `p
builtin "P" ≔ π;

constant symbol ⊤ : Prop; // \top
constant symbol top : π ⊤;
constant symbol ⊥ : Prop; // \bot
constant symbol ⊥ₑ [p] : π ⊥ → π p;
constant symbol ⇒ : Prop → Prop → Prop; // =>
notation ⇒ infix right 5;
rule π ($p ⇒ $q) ↪ π $p → π $q;
symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg
constant symbol ∧ : Prop → Prop → Prop; // /\ or \wedge
notation ∧ infix left 7;
constant symbol ∧ᵢ [p q] : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ [p q] : π (p ∧ q) → π p;
symbol ∧ₑ₂ [p q] : π (p ∧ q) → π q;
constant symbol ∨ : Prop → Prop → Prop; // \/ or \vee
notation ∨ infix left 6;
constant symbol ∨ᵢ₁ [p q] : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ [p q] : π q → π (p ∨ q);
symbol ∨ₑ [p q r] : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

constant symbol = [a] : τ a → τ a → Prop;
notation = infix 10;
constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

symbol nat:Set;
symbol O:τ nat;
symbol +:τ(nat ↦ nat ↦ nat);
notation + infix right 20;
rule $x + O ↪ $x;
symbol f:τ(nat ↦ (nat ↦ nat) ↦ nat);
symbol add_com a b : π(a + b = b + a);

symbol test1 a b : π (f (a + b) (λ _, O) = f (b + a) (λ _, O))
≔ begin
  assume a b;
  rewrite add_com;
  reflexivity
end;

symbol test2' a b : π (f (a + b) (λ _, O) = f (b + a) (λ _, O))
≔ begin
  assume a b;
  simplify;
  set p ≔ (a + b);
  set g ≔ (a + b + O + O);
  //type p;
  //compute p;
  //compute g;
  have foo: π (p = g) {
    //simplify p;
    //simplify q;
    //compute p;
    //compute g;
    reflexivity;
  };
  rewrite add_com;
  reflexivity
end;
