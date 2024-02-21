constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE; // `p
builtin "P" ≔ π;

constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;
builtin "T" ≔ τ;

constant symbol ⊥ : Prop; // \bot

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5; // =>
rule π ($p ⇒ $q) ↪ π $p → π $q;

symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg
notation ¬ prefix 35;

constant symbol ∀ [a] : (τ a → Prop) → Prop; notation ∀ quantifier; // !! or \forall
rule π (∀ $f) ↪ Π x, π ($f x);

injective symbol πᶜ p ≔ π (¬ ¬ p);

flag "print_implicits" on;
flag "print_domains" on;
//flag "print_meta_types" on;

symbol ∀ᶜ [a] p ≔ `∀ x : τ a, ¬ ¬ (p x); notation ∀ᶜ quantifier;

//debug +hiuta;
opaque symbol ∀ᶜᵢ p : (Π x, πᶜ (p x)) → πᶜ (∀ᶜ p) ≔
begin
  print;
  //debug -hiuta;
  assume p Hnnpx Hnnnpx;
  apply Hnnnpx;
  assume x Hnnp;
  apply Hnnpx x;
  assume Hnp;
  apply Hnnp;
  apply Hnp;
end;

print ∀ᶜᵢ;
