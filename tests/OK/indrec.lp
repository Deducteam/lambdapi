// example of inductive-recursive type definition

// assumptions

constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;

injective symbol π : Prop → TYPE;
builtin "P" ≔ π;

constant symbol ⊤ : Prop;
constant symbol top : π ⊤;

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 10;
constant symbol ∧ᵢ p q : π p → π q → π(p ∧ q);

constant symbol ℕ : TYPE;

symbol ≠ : ℕ → ℕ → Prop; notation ≠ infix 20;

// lists without duplicated elements

constant symbol L : TYPE;

symbol ∉ : ℕ → L → Prop; notation ∉ infix 20;

constant symbol nil : L;
constant symbol cons x l : π(x ∉ l) → L;

rule _ ∉ nil ↪ ⊤
with $x ∉ cons $y $l _ ↪ $x ≠ $y ∧ $x ∉ $l;

symbol ind_L p : π(p nil) → (Π x l, π(p l) → Π h, π(p (cons x l h)))
                 → Π l, π(p l);

rule ind_L _ $a _ nil ↪ $a
with ind_L $p $a $b (cons $x $l $h) ↪ $b $x $l (ind_L $p $a $b $l) $h;

/* syntax ?

inductive L : TYPE ≔
| nil : L
| cons x l : π(x ∉ l) → L
with infix 20 symbol ∉ : ℕ → L → Prop
with _ ∉ nil ↪ ⊤
with $x ∉ cons $y $l _ ↪ $x ≠ $y ∧ $x ∉ $l;
*/
