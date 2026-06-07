symbol Prop: TYPE;
builtin "Prop" ≔ Prop;
injective symbol π: Prop → TYPE;
builtin "P" ≔ π;

symbol ⊤: Prop;
constant symbol ⊤ᵢ : π ⊤;

constant symbol ∧ : Prop → Prop → Prop;
notation ∧ infix right 7;
constant symbol ∧ᵢ [p q: Prop] : π p → π q → π (p ∧ q);
constant symbol ∧ₑ₁ [p q: Prop] : π (p ∧ q) → π p;
constant symbol ∧ₑ₂ [p q: Prop] : π (p ∧ q) → π q;

constant symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 5;
rule π ($p ⇒ $q) ↪ π $p → π $q;

symbol ⇔ (p q: Prop): Prop ≔ (p ⇒ q) ∧ (q ⇒ p);
notation ⇔ infix right 5;

opaque ⇔;

rule π ($p ⇔ $q) ↪ π (($p ⇒ $q) ∧ ($q ⇒ $p));
unif_rule ($p ⇔ $q) ≡ ($r1 ∧ $r2) ↪ [$r1 ≡ @⇒ $p $q; $r2 ≡ @⇒ $q $p];

constant symbol Set: TYPE;
injective symbol τ: Set → TYPE;

constant symbol Nat: TYPE;
constant symbol nat: Set;
rule τ nat ↪ Nat;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a
| ⸬ : τ a → 𝕃 a → 𝕃 a;

notation ⸬ infix right 20;
constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;


symbol map_ty ≔ τ nat → Prop;
symbol sem0 : 𝕃 nat → map_ty → Prop;
symbol sem : 𝕃 nat → map_ty → Prop;

rule sem0  □ _ ↪  ⊤
with sem0 ($i ⸬  $l) $m ↪ $m $i ∧ sem0 $l $m;

rule sem  □ _ ↪  ⊤
with sem ($i ⸬  □) $m ↪ $m $i
with sem ($i ⸬ $j ⸬ $l) $m ↪ $m $i ∧ sem ($j ⸬ $l) $m;

symbol sem_sem0 (m: τ nat → Prop) (l: 𝕃 nat): π (sem l m ⇔ sem0 l m) ≔
begin
  assume m;
  induction { simplify; apply  ∧ᵢ (λ p,p) (λ p,p) }
            { assume x0 l h; simplify;
              apply ∧ᵢ
              { generalize l;
                induction
                { simplify; assume h1 h2; apply ∧ᵢ h2 ⊤ᵢ}
                { assume x l h1 h2; simplify sem; assume h3;
                  refine ∧ᵢ (∧ₑ₁ h3) _;
print; // loop ...
                  admit; // refine (∧ₑ₁ h2 (∧ₑ₂ h3));
                };
              }
              { generalize l;
                induction
                { simplify; assume h1 h2; apply ∧ₑ₁ h2}
                { assume x l h1 h2; simplify sem; assume h3;
                  refine ∧ᵢ (∧ₑ₁ h3) _;
print;
// loop ...
                  refine (∧ₑ₂ h2 (∧ₑ₂ h3));
                };
              };
            };
end;
