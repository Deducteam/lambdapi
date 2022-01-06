// Polymorphic lists

require open Logic.TFF.Set Logic.TFF.Prop Logic.TFF.Main Logic.TFF.Eq
             Logic.TFF.Nat;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 4;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

// Length of a list

symbol length [a] : 𝕃 a → ℕ;

rule length □ ↪ 0
with length (_ ⸬ $l) ↪ s (length $l);

// Concatenation of two lists

symbol ⋅ [a] : 𝕃 a → 𝕃 a → 𝕃 a;

notation ⋅ infix right 15; // \cdot

assert a (x y z:𝕃 a) ⊢ x ⋅ y ⋅ z ≡ x ⋅ (y ⋅ z);
assert a x l m ⊢ x ⸬ l ⋅ m ≡ x ⸬ (l ⋅ m);

rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);

opaque symbol concat_nil [a] (l:𝕃 a) : π(l ⋅ □ = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l' h; simplify; rewrite h; reflexivity }
end;

rule $m ⋅ □ ↪ $m;

opaque symbol length_concat [a] (l m : 𝕃 a) :
  π(length (l ⋅ m) = length l + length m) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l' h m; simplify; rewrite h; reflexivity }
end;

rule length ($l ⋅ $m) ↪ length $l + length $m;

opaque symbol concat_assoc [a] (l m n : 𝕃 a) : π((l ⋅ m) ⋅ n = l ⋅ (m ⋅ n)) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l' h m n; simplify; rewrite h; reflexivity }
end;

rule ($l ⋅ $m) ⋅ $n ↪ $l ⋅ ($m ⋅ $n);

// List reversal

symbol rev [a] : 𝕃 a → 𝕃 a;

rule rev □ ↪ □
with rev ($x ⸬ $l) ↪ rev $l ⋅ ($x ⸬ □);

opaque symbol rev_concat [a] (l m : 𝕃 a) : π(rev (l ⋅ m) = rev m ⋅ rev l) ≔
begin
  assume a; induction
  { simplify; reflexivity }
  { assume x l h m; simplify; rewrite h; reflexivity }
end;

rule rev ($l ⋅ $m) ↪ rev $m ⋅ rev $l;

opaque symbol rev_idem [a] (l :𝕃 a) : π(rev (rev l) = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l h; simplify; rewrite h; reflexivity }
end;

rule rev (rev $l) ↪ $l;

opaque symbol length_rev [a] (l : 𝕃 a) : π(length (rev l) = length l) ≔
begin
  assume a; induction
  { simplify; reflexivity }
  { assume x l h; simplify; rewrite h; reflexivity }
end;

rule length (rev $l) ↪ length $l;
