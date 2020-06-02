/////////////////////////////
// Configuration
/////////////////////////////

constant symbol Prop : TYPE      // Type of propositions
set declared "π"
injective symbol π : Prop → TYPE // Interpretation of propositions in TYPE

set builtin "Prop"     ≔ Prop
set builtin "P"     ≔ π

constant symbol Set : TYPE       // Type of set codes
set declared "τ"
injective symbol τ : Set → TYPE  // Interpretation of set codes in TYPE

/////////////////////////////
// Equality
/////////////////////////////
constant symbol eq {a} : τ a → τ a → Prop
set infix 8 "=" ≔ eq
constant symbol eq_refl {a} (x : τ a) : π (x = x)
constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Πp, π (p y) → π (p x)

// Set builtins for the rewrite tactic
set builtin "T"     ≔ τ
set builtin "eq"    ≔ eq
set builtin "refl"  ≔ eq_refl
set builtin "eqind" ≔ eq_ind

/////////////////////////////
// Some examples of inductive types
/////////////////////////////

constant symbol nat : Set // Natural number
inductive Nat : TYPE ≔
 | z    : Nat
 | succ : Nat → Nat
rule Nat ↪ τ nat

type ind_Nat // Induction principle
assert ind_Nat :
  Πp:Nat → Prop, π(p z) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)

assert z : Nat // Examples
assert succ z : Nat
assert succ (succ (succ z)) : Nat

constant symbol list : Set // Lists
inductive List : TYPE ≔
 | nil  : List
 | cons : Nat → List → List
rule List ↪ τ list

type ind_List // Induction principle
assert ind_List :
  Π(p:List → Prop), π(p nil) → (Πx l,π(p l) → π(p(cons x l))) → Πl,π(p l)

assert nil : List // Examples
assert cons (succ (succ (succ z))) nil : List
assert cons (succ (succ (succ z))) (cons (succ z) nil) : List
assert cons (succ (succ (succ z))) (cons (succ z) (cons z nil)) : List

/////////////////////////////
// Some proofs
/////////////////////////////

// About natural numbers
set builtin "0"  ≔ z
set builtin "+1" ≔ succ

symbol plus : Nat → Nat → Nat
set infix left 6 "+" ≔ plus
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y)

theorem plus_0_n : Πn, π ((0 + n) = n)
proof
  assume n
  reflexivity
qed

theorem plus_n_0 : Πn, π ((n + 0) = n)
proof
  assume n
  refine ind_Nat (λz, (z + 0) = z) _ _ _
  // Case n = O
  refine eq_refl 0
  // Case = S n'
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
qed

// About lists
symbol length : List → Nat
rule length nil ↪ 0
 with length (cons _ $l) ↪ succ (length $l)

symbol app : List → List → List
rule  app      nil     $m ↪ $m
 with app (cons $x $l) $m ↪ cons $x (app $l $m)

theorem length_app :
  Π(l1 l2 : List), π ((length l1 + length l2) = length (app l1 l2))
proof
  assume l1 l2
  apply ind_List
        (λz, (length z+length l2) = length (app z l2)) _ _ l1
  reflexivity
  assume x l2 IHl1
  simpl rewrite IHl1 reflexivity
qed
