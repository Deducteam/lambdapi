constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "P" ≔ π;
constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;
builtin "T" ≔ τ;
inductive ℕ : TYPE ≔ // `dN
| 0 : ℕ
| s : ℕ → ℕ;
constant symbol nat : Set;
rule τ nat ↪ ℕ;

symbol is0 : ℕ → Prop;
builtin "0"  ≔ 0;
builtin "+1" ≔ s;
symbol one ≔ s 0;

symbol + : ℕ → ℕ → ℕ;
notation + infix right 20;
rule 0 + $y ↪ $y
with s $x + $y ↪ s ($x + $y);

symbol × : ℕ → ℕ → ℕ; // \times
notation × infix right 30;
rule 0 × _  ↪ 0
with s $x × $y ↪ $y + $x × $y;

constant symbol ∃ [a] : (τ a → Prop) → Prop;
notation ∃ quantifier;
builtin "ex" ≔ ∃;

constant symbol ∀ [a] : (τ a → Prop) → Prop;
builtin "all" ≔ ∀;
constant symbol = [a] : τ a → τ a → Prop;
notation = infix 10;
builtin "eq"    ≔ =;
symbol =-refl x : π(x = x);
constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol imp        : Prop → Prop → Prop;
builtin "imp"   ≔ imp; // écrire regle
rule π (imp $a $b) ↪ π $a → π $b;

symbol zero_eq_zero : π (∃ (λ y : τ nat, (0 + y = 0))) ≔
begin
  print;
  simplify +;
  print;
  skolem;
  
  print;

end;