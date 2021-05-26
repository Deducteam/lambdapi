// Type of set codes for quantifying other sets (polymorphism)

constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE;

builtin "T" ≔ τ;

// Propositional logic

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// Interpretation of propositions in TYPE

injective symbol π : Prop → TYPE;

builtin "P" ≔ π;

// Implication

constant symbol ⇒ : Prop → Prop → Prop; // =>

notation ⇒ infix right 5;

rule π ($p ⇒ $q) ↪ π $p → π $q;

// Universal quantification

constant symbol ∀ {a} : (τ a → Prop) → Prop;

notation ∀ quantifier;

rule π (∀ $f) ↪ Π x, π ($f x);

// polymorphic Leibniz equality

constant symbol = {a} : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl {a} (x:τ a) : π (x = x);
constant symbol ind_eq {a} {x y:τ a} : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

// Natural numbers

inductive ℕ : TYPE ≔
| zero : ℕ
| s : ℕ → ℕ;

// set code for ℕ

constant symbol nat : Set;

rule τ nat ↪ ℕ;

// Enabling the use of decimal notation

builtin "0"  ≔ zero;
builtin "+1" ≔ s;

// Addition

symbol + : ℕ → ℕ → ℕ;

notation + infix left 20;

rule 0 + $y ↪ $y
with s $x + $y ↪ s ($x + $y);

// Addition is commutative

opaque symbol add0r x : π (x + 0 = x) ≔
begin
  induction;
  // case x = 0
  reflexivity;
  // case x = s x'
  assume x' h; simplify; rewrite h; reflexivity;
end;

rule $x + 0 ↪ $x;

opaque symbol addsr x y : π (x + s y = s (x + y)) ≔
begin
  induction;
  // case x = 0
  reflexivity;
  // case x = s x'
  assume x' h y; simplify; rewrite h; reflexivity;
end;

rule $x + s $y ↪ s ($x + $y);

opaque symbol add_com x y : π (x + y = y + x) ≔
begin
  induction;
  // case x = 0
  reflexivity;
  // case x = s x'
  simplify; assume x' h y; rewrite h; reflexivity;
end;

// Addition is associative

opaque symbol add_assoc x y z : π ((x + y) + z = x + (y + z)) ≔
begin
  induction;
  // case x = 0
  reflexivity;
  // case x = s x'
  assume x' h y z; simplify; rewrite h; reflexivity;
end;

rule ($x + $y) + $z ↪ $x + ($y + $z);

// test 1: rewrite left

opaque symbol test1 a b c : π (a + (b + c) = c + (a + b))
≔ begin
  assume a b c;
  rewrite left add_assoc;
  rewrite add_com;
  reflexivity;
end;

// test 2

symbol f : ℕ → (ℕ → ℕ) → ℕ;

symbol test2 a b : π (f (a + b) (λ _, 0) = f (b + a) (λ _, 0))
≔ begin
  assume a b;
  rewrite add_com;
  reflexivity;
end;
