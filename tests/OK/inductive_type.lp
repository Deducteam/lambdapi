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

//////////////////////
// Boolean type
//////////////////////

constant symbol bool : Set       // Type of booleans
set declared "𝔹"
definition 𝔹 ≔ τ bool
constant symbol true  : 𝔹
constant symbol false : 𝔹

/////////////////////////////
// Some examples of inductive types
/////////////////////////////
set debug +h

inductive {|sum|} : Π(A:Set) (B:Set), TYPE ≔
  inl : ΠA B, τ A → {|sum|} A B
| inr : ΠA B, τ B → {|sum|} A B

type {|ind_sum|}

set declared "ℕ"
inductive ℕ : TYPE ≔
 | cons1 : ℕ
 | cons2 : ℕ → ℕ

//set declared "ind_ℕ"
//symbol ind_ℕ : ℕ
type ind_ℕ

inductive RGB : TYPE ≔
 | red   : RGB
 | green : RGB
 | blue  : RGB

type ind_RGB

inductive Color : TYPE ≔
 | black : Color
 | white : Color
 | primary : Π(p : RGB), Color

type ind_Color

///////////////// Natural number

constant symbol nat : Set
inductive Nat : TYPE ≔
 | z    : Nat
 | succ : Nat → Nat
rule Nat ↪ τ nat

type ind_Nat // Induction principle
assert ind_Nat :
  Πp:Nat → Prop, π(p z) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)

symbol p : Nat → Prop // Tests about inductive rules
symbol pizero : π (p z)
symbol x : Nat
symbol pisucc : Πx, π (p x) → π (p (succ x))
assert ind_Nat p pizero _ z ≡ pizero
assert ind_Nat p pizero pisucc (succ x) ≡ pisucc x (ind_Nat p pizero pisucc x)

assert z : Nat // Examples
assert succ z : Nat
assert succ (succ (succ z)) : Nat

////////////////////// Lists

constant symbol list : Set
inductive List : TYPE ≔
 | nil  : List
 | cons : Nat → List → List
rule List ↪ τ list

type ind_List // Induction principle
assert ind_List :
  Π(p:List → Prop), π(p nil) → (Πx l,π(p l) → π(p(cons x l))) → Πl,π(p l)

symbol pList : List → Prop // Tests about inductive rules
symbol pinil : π (pList nil)
symbol l : List
symbol picons : Πx l, π (pList l) → π (pList (cons x l))
assert ind_List pList pinil _ nil ≡ pinil
assert ind_List pList pinil picons (cons x l)
     ≡ picons x l (ind_List pList pinil picons l)

assert nil : List // Examples
assert cons (succ (succ (succ z))) nil : List
assert cons (succ (succ (succ z))) (cons (succ z) nil) : List
assert cons (succ (succ (succ z))) (cons (succ z) (cons z nil)) : List

///////////////////// Polymorphic list

inductive L : Πa:Set, TYPE ≔
 | nilL  : Πa, L a
 | consL : Πa, τ a → L a → L a

type ind_L // Induction principle
assert ind_L :
  Πp, (Πa, π(p a (nilL a))) → (Πa x l, π(p a l) → π(p a (consL a x l))) → Πa l, π(p a l)

symbol pL : Πa, L a → Prop // Tests about inductive rules
symbol pinilL : Πa, π (pL a (nilL a))
symbol a : Set
symbol x0 : τ a
symbol l0 : L a
symbol piconsL : Πa x l, π (pL a l) → π (pL a (consL a x l))
assert ind_L pL pinilL _ a (nilL a) ≡ pinilL a
assert ind_L pL pinilL piconsL a (consL a x0 l0)
     ≡ piconsL a x0 l0 (ind_L pL pinilL piconsL a l0)

assert nilL a : L a // Examples
assert consL nat (succ (succ (succ z))) (nilL nat) : L nat
assert consL nat (succ (succ (succ z))) (consL nat (succ z) (nilL nat)) : L nat
assert consL nat (succ (succ (succ z))) (consL nat (succ z) (consL nat z (nilL nat))) : L nat
assert consL bool true (nilL bool) : L bool

//////////////////// Vector

symbol A : TYPE
inductive Vec : Nat → TYPE ≔
 | nil_vec   : Vec z
 | cons_vec  : Πn, A → Vec n → Vec (succ n)

type ind_Vec // Induction principle
assert ind_Vec :
 Πp, π(p z nil_vec) → (Πn x v, π(p n v) → π(p (succ n) (cons_vec n x v))) → Πn v, π(p n v)

symbol pV : Πn, Vec n → Prop // Tests about inductive rules
symbol pinil_vec : π (pV z nil_vec)
symbol n : Nat
symbol xV : A
symbol v : Vec n
symbol picons_vec : Πn x v, π(pV n v) → π(pV (succ n) (cons_vec n x v))
assert ind_Vec pV pinil_vec _ z nil_vec ≡ pinil_vec
assert ind_Vec pV pinil_vec picons_vec (succ n) (cons_vec n xV v)
     ≡ picons_vec n xV v (ind_Vec pV pinil_vec picons_vec n v)

assert nil_vec : Vec z // Examples
assert cons_vec (succ z) xV (cons_vec z xV nil_vec) : Vec (succ (succ z))

/////////////////// Polymorphic vector

inductive Vec_param : Π(a : Set), Π(n : Nat), TYPE ≔
 | nil_vec_p   : Πa, Vec_param a z
 | cons_vec_p  : Πa n (_:τ a), Vec_param a n → Vec_param a (succ n)

type ind_Vec_param // Induction principle
assert ind_Vec_param :
  Πp, (Πa, π(p a z (nil_vec_p a))) → (Πa n x v, π(p a n v) → π(p a (succ n) (cons_vec_p a n x v))) → Πa n v, π(p a n v)

symbol pV_p : Πa n, Vec_param a n → Prop // Tests about inductive rules
symbol pinil_vec_p : Πa, π (pV_p a z (nil_vec_p a))
symbol xV_p : τ a
symbol v_p : Vec_param a n
symbol picons_vec_p : Πa n x v, π(pV_p a n v) → π(pV_p a (succ n) (cons_vec_p a n x v))
assert ind_Vec_param pV_p pinil_vec_p _ a z (nil_vec_p a) ≡ pinil_vec_p a
assert ind_Vec_param pV_p pinil_vec_p picons_vec_p a (succ n) (cons_vec_p a n xV_p v_p)
     ≡ picons_vec_p a n xV_p v_p (ind_Vec_param pV_p pinil_vec_p picons_vec_p a n v_p)

assert nil_vec_p a : Vec_param a z // Examples
assert nil_vec_p nat : Vec_param nat z
assert cons_vec_p nat (succ z) (succ (succ (succ z))) (cons_vec_p nat z z (nil_vec_p nat)) : Vec_param nat (succ (succ z))
assertnot cons_vec_p nat (succ z) (succ (succ (succ z))) (cons_vec_p nat z true (nil_vec_p nat)) : Vec_param nat (succ (succ z))
assert cons_vec_p bool (succ z) false (cons_vec_p bool z true (nil_vec_p bool)) : Vec_param bool (succ (succ z))

////////////////// Example of mutual inductive type

// inductive Expr : Set ≔
//    Lit : τ nat   → Expr
//  | Add : Expr  → Expr → Expr
//  | If  : BExpr → Expr → Expr → Expr
// with BExpr : Set :=
//  | BLit  : τ bool  → BExpr
//  | And   : BExpr → BExpr → BExpr
//  | Not   : BExpr → BExpr
//  | Equal : Expr  → Expr → BExpr

////////////////// Type Bush (nested inductive type)

symbol bush : Set →  Set
inductive Bush : Π(_:Set), TYPE ≔
 | BNil : Πa, Bush a
 | BCons : Πa, τ a → Bush (bush a) → Bush a
rule Bush $a ↪ τ (bush $a)

type ind_Bush // Induction principle
assert ind_Bush :
  Πp, (Πa, π(p a (BNil a))) → (Πa x l, π(p (bush a) l) → π(p a (BCons a x l))) → Πa l, π(p a l)

symbol pB : Πa, Bush a → Prop // Tests about inductive rules
symbol piBNil : Πa, π (pB a (BNil a))
symbol B : Bush (bush a)
symbol piBCons : Πa x l, π (pB (bush a) l) → π (pB a (BCons a x l))
assert ind_Bush pB piBNil _ a (BNil a) ≡ piBNil a
assert ind_Bush pB piBNil piBCons a (BCons a x0 B)
     ≡ piBCons a x0 B (ind_Bush pB piBNil piBCons (bush a) B)

assert BNil a : Bush a // Examples
assert consL nat (succ (succ (succ z))) (nilL nat) : L nat
assert consL nat (succ (succ (succ z))) (consL nat (succ z) (nilL nat)) : L nat
assert consL nat (succ (succ (succ z))) (consL nat (succ z) (consL nat z (nilL nat))) : L nat
assert consL bool true (nilL bool) : L bool

///////////////// An example of the heterogenous dependent family

inductive fin : Nat → TYPE ≔
  | new : Πn, fin (succ n)
  | inj : Πn, fin n → fin (succ n)

type ind_fin // Induction principle
assert ind_fin : Πp, (Πn, π (p (succ n) (new n))) → (Πn f, π (p n f) → π (p (succ n) (inj n f))) → Πn f, π (p n f)

symbol pF : Πn, fin n → Prop // Tests about inductive rules
symbol pinew : Πn, π (pF (succ n) (new n))
symbol f : fin n
symbol piinj : Πn f, π (pF n f) → π (pF (succ n) (inj n f))
assert ind_fin pF pinew _ (succ n) (new n) ≡ pinew n
assert ind_fin pF pinew piinj (succ n) (inj n f)
     ≡ piinj n f (ind_fin pF pinew piinj n f)

assert new n : fin (succ n) // Examples
assert inj (succ n) (new n) : fin (succ (succ n))

///////////////// Bounded List

symbol le : Nat → Nat → Prop
set infix left 6 "≤" ≔ le

//inductive ≤ : Π(n:τ nat), Nat → Prop ≔
//  | le_n : Πn, π (n ≤ n)
//  | le_S : Πn m:τ nat, π (n ≤ m) → π (n ≤ (succ m))

inductive listb : Π(bound : τ nat), TYPE ≔
   Bnil  : Πbound, listb bound
 | Bcons : Πbound x, π (x ≤ bound) → listb bound → listb bound

type ind_listb // Induction principle
assert ind_listb :
Πp, (Πbound, π(p bound (Bnil bound))) →
(Πbound x (prf:π (x ≤ bound)) l, π(p bound l) → π(p bound (Bcons bound x prf l))) → 
Πbound l, π(p bound l)

symbol pbound : Πbound, listb bound → Prop // Tests about inductive rules
symbol piBnil : Πbound, π(pbound bound (Bnil bound))
symbol bound : τ nat
symbol prf : π (x ≤ bound)
symbol lb : listb bound
symbol piBcons : Πbound x (prf:π (x ≤ bound)) l, π(pbound bound l) → π(pbound bound (Bcons bound x prf l))
assert ind_listb pbound piBnil _ bound (Bnil bound) ≡ piBnil bound
assert ind_listb pbound piBnil piBcons bound (Bcons bound x prf lb)
     ≡ piBcons bound x prf lb (ind_listb pbound piBnil piBcons bound lb)

assert Bnil bound : listb bound // Examples
assert Bcons bound x prf (Bnil bound) : listb bound

///////////////// Predicat even

inductive even : Nat → TYPE ≔
| O_even      : even z
| plus_2_even : Πn:τ nat, even n → even (succ (succ n))

type ind_even

///////////////// Forest

// TODO ...

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
