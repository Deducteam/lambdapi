/////////////////////////////
// Configuration
/////////////////////////////

constant symbol Prop : TYPE;      // Type of propositions
injective symbol π : Prop → TYPE; // Interpretation of propositions in TYPE

set builtin "Prop"     ≔ Prop;
set builtin "P"     ≔ π;

constant symbol Set : TYPE;       // Type of set codes
injective symbol τ : Set → TYPE;  // Interpretation of set codes in TYPE

/////////////////////////////
// Equality
/////////////////////////////

constant symbol eq {a} : τ a → τ a → Prop;
set infix 8 "=" ≔ eq;
constant symbol eq_refl {a} (x : τ a) : π (x = x);
constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Π p, π (p y) → π (p x);

// Set builtins for the rewrite tactic
set builtin "T"     ≔ τ;
set builtin "eq"    ≔ eq;
set builtin "refl"  ≔ eq_refl;
set builtin "eqind" ≔ eq_ind;

/////////////////////////////
// Some examples of inductive types
/////////////////////////////

////////////////// Primary color

inductive RGB : TYPE ≔
 | ℝ  : RGB
 | 𝔾 : RGB
 | Blue : RGB;

assert ⊢ ind_RGB : // Induction principle
  Π p : RGB → Prop,
  π (p ℝ) → π (p 𝔾) → π (p Blue) →
  Π x, π (p x);

symbol pRGB : RGB → Prop; // Tests about inductive rules
symbol piR : π (pRGB ℝ);
symbol piG : π (pRGB 𝔾);
symbol piB: π (pRGB Blue);
assert ⊢ ind_RGB pRGB piR _ _  ℝ ≡ piR;
assert ⊢ ind_RGB pRGB _ piG _ 𝔾 ≡ piG;
assert ⊢ ind_RGB pRGB _ _ piB Blue ≡ piB;

assert ⊢ ℝ    : RGB; // Examples
assert ⊢ 𝔾   : RGB;
assert ⊢ Blue : RGB;

////////////////// Type color

inductive Color : TYPE ≔
 | black : Color
 | white : Color
 | primary : RGB → Color;

assert ⊢ ind_Color : // Induction principle
  Π p : Color → Prop,
  π (p black) → π (p white) → (Π x, π (p (primary x))) →
  Π x, π (p x);

symbol pC : Color → Prop; // Tests about inductive rules
symbol piblack : π (pC black);
symbol piwhite : π (pC white);
symbol rgb : RGB;
symbol piprimary: Π x, π (pC (primary x));
assert ⊢ ind_Color pC piblack piwhite piprimary black ≡ piblack;
assert ⊢ ind_Color pC piblack piwhite piprimary white ≡ piwhite;
assert ⊢ ind_Color pC piblack piwhite piprimary (primary rgb) ≡ piprimary rgb;

assert ⊢ white : Color; // Examples
assert ⊢ black : Color;
assert ⊢ primary ℝ : Color;
assert ⊢ primary 𝔾 : Color;
assert ⊢ primary Blue : Color;

////////////////// Boolean type

constant symbol bool : Set;
inductive 𝔹 : TYPE ≔
 | true  : 𝔹
 | false : 𝔹;
rule 𝔹 ↪ τ bool;

//assert ind_𝔹 : // Induction principle
//  Π p : 𝔹 → Prop,
//  π (p true) → π (p false) →
//  Π b, π (p b)

symbol pBool : 𝔹 → Prop; // Tests about inductive rules
symbol pitrue  : π (pBool true);
symbol pifalse : π (pBool false);
// assert ind_𝔹 p𝔹 pitrue pifalse true  ≡ pitrue
// assert ind_𝔹 p𝔹 pitrue pifalse false ≡ pifalse

assert ⊢ true  : 𝔹; // Examples
assert ⊢ false : 𝔹;

////////////////// False (not predicate one)

inductive False : TYPE ≔;

assert ⊢ ind_False : // Induction principle
 Π(p:False → Prop) (f : False), π (p f);

///////////////// Natural number

constant symbol nat : Set;
inductive Nat : TYPE ≔
 | z    : Nat
 | succ : Nat → Nat;
rule Nat ↪ τ nat;

assert ⊢ ind_Nat : // Induction principle
  Π p:Nat → Prop, π(p z) → (Π x, π (p x) → π (p (succ x))) → Π x, π (p x);

symbol p : Nat → Prop; // Tests about inductive rules
symbol pizero : π (p z);
symbol x : Nat;
symbol pisucc : Π x, π (p x) → π (p (succ x));
assert ⊢ ind_Nat p pizero _ z ≡ pizero;
assert ⊢ ind_Nat p pizero pisucc (succ x) ≡ pisucc x (ind_Nat p pizero pisucc x);

assert ⊢ z : Nat; // Examples
assert ⊢ succ z : Nat;
assert ⊢ succ (succ (succ z)) : Nat;

// About natural numbers
set builtin "0"  ≔ z;
set builtin "+1" ≔ succ;

symbol plus : Nat → Nat → Nat;
set infix left 6 "+" ≔ plus;
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y);

symbol mult : Nat → Nat → Nat;
set infix left 7 "×" ≔ mult;
rule       0 × _  ↪ 0
with succ $x × $y ↪ $y + $x × $y;

symbol le : Nat → Nat → Prop;
set infix left 6 "≤" ≔ le;

//inductive ≤ : Π(n:τ nat), Nat → Prop ≔
//  | le_n : Π n, π (n ≤ n)
//  | le_S : Π n m:τ nat, π (n ≤ m) → π (n ≤ (succ m))

////////////////////// List of natural numbers

constant symbol list : Set;
inductive List : TYPE ≔
 | nil  : List
 | cons : Nat → List → List;
rule List ↪ τ list;

assert ⊢ ind_List : // Induction principle
  Π(p:List → Prop), π(p nil) → (Π x l,π(p l) → π(p(cons x l))) → Π l,π(p l);

symbol pList : List → Prop; // Tests about inductive rules
symbol pinil : π (pList nil);
symbol l : List;
symbol picons : Π x l, π (pList l) → π (pList (cons x l));
assert ⊢ ind_List pList pinil _ nil ≡ pinil;
assert ⊢ ind_List pList pinil picons (cons x l)
     ≡ picons x l (ind_List pList pinil picons l);

assert ⊢ nil : List; // Examples
assert ⊢ cons (succ (succ (succ z))) nil : List;
assert ⊢ cons (succ (succ (succ z))) (cons (succ z) nil) : List;
assert ⊢ cons (succ (succ (succ z))) (cons (succ z) (cons z nil)) : List;

///////////////// Couple of natural numbers

inductive nat_prod : TYPE ≔
 | prod : Nat → Nat → nat_prod;

assert ⊢ ind_nat_prod : // Induction principle
Π p : nat_prod → Prop,
(Π x0 x1, π (p (prod x0 x1))) →
Π x, π (p x);

symbol pNP : nat_prod → Prop; // Tests about inductive rules
symbol piprod : Π x0 x1, π (pNP (prod x0 x1));
symbol nat1 : Nat;
symbol nat2 : Nat;
assert ⊢ ind_nat_prod pNP piprod (prod nat1 nat2) ≡ piprod nat1 nat2;

assert ⊢ prod z z : nat_prod; // Examples
assert ⊢ prod (succ (succ (succ z))) z : nat_prod;
assert ⊢ prod (succ (succ (succ z))) (succ z) : nat_prod;
assert ⊢ prod (succ z) (succ (succ (succ z))) : nat_prod;

///////////////// Binary tree

inductive Tree : TYPE ≔
  | leaf : Tree
  | consTree : Tree → Nat → Tree → Tree;

assert ⊢ ind_Tree : Π p, // Induction principle
π (p leaf) →
(Π t1, π (p t1) → Π x t2, π (p t2) → π (p (consTree t1 x t2))) →
Π t, π (p t);

symbol pT : Tree → Prop; // Tests about inductive rules
symbol pileaf : π (pT leaf);
symbol t1 : Tree;
symbol t2 : Tree;
symbol piconsTree : Π t1, π (pT t1) → Π x t2, π (pT t2) → π (pT (consTree t1 x t2));
assert ⊢ ind_Tree pT pileaf piconsTree leaf ≡ pileaf;
assert ⊢ ind_Tree pT pileaf piconsTree (consTree t1 x t2)
     ≡ piconsTree t1 (ind_Tree pT pileaf piconsTree t1)
                x t2 (ind_Tree pT pileaf piconsTree t2);

assert ⊢ leaf : Tree; // Examples
assert ⊢ consTree (consTree leaf z leaf) z (consTree leaf (succ z) leaf) : Tree;
assert ⊢ consTree (consTree (consTree leaf z leaf) z leaf) z (consTree leaf z leaf) : Tree;

///////////////////// Polymorphic list

inductive L : Set → TYPE ≔
 | nilL  : Π a, L a
 | consL : Π a, τ a → L a → L a;

assert ⊢ ind_L : // Induction principle
  Π p, (Π a, π(p a (nilL a))) → (Π a x l, π(p a l) → π(p a (consL a x l))) → Π a l, π(p a l);

symbol pL : Π a, L a → Prop; // Tests about inductive rules
symbol pinilL : Π a, π (pL a (nilL a));
symbol a : Set;
symbol xa : τ a;
symbol la : L a;
symbol piconsL : Π a x l, π (pL a l) → π (pL a (consL a x l));
assert ⊢ ind_L pL pinilL _ a (nilL a) ≡ pinilL a;
assert ⊢ ind_L pL pinilL piconsL a (consL a xa la)
     ≡ piconsL a xa la (ind_L pL pinilL piconsL a la);

assert ⊢ nilL a : L a; // Examples
assert ⊢ consL nat (succ (succ (succ z))) (nilL nat) : L nat;
assert ⊢ consL nat (succ (succ (succ z))) (consL nat (succ z) (nilL nat)) : L nat;
assert ⊢ consL nat (succ (succ (succ z))) (consL nat (succ z) (consL nat z (nilL nat))) : L nat;
assert ⊢ consL bool true (nilL bool) : L bool;

////////////////// Type sum

inductive {|sum|} : Set → Set → TYPE ≔
 | {|inl_sum|} : Π A B, τ A → {|sum|} A B
 | inr : Π A B, τ B → {|sum|} A B;

assert ⊢ {|ind_sum|} : Π p, // Induction principle
(Π A B a, π (p A B ({|inl_sum|} A B a))) →
(Π A B b, π (p A B (inr A B b))) →
Π A B s, π (p A B s);

symbol pS : Π(A:Set) (B:Set), {|sum|} A B → Prop;// Tests about inductive rules
symbol G : Set;
symbol g : τ G;
symbol D : Set;
symbol d : τ D;
symbol piinl : Π A B a, π (pS A B ({|inl_sum|} A B a));
symbol piinr : Π A B b, π (pS A B (inr A B b));

assert ⊢ {|ind_sum|} pS piinl piinr G D ({|inl_sum|} G D g)
     ≡ piinl G D g;
assert ⊢ {|ind_sum|} pS piinl piinr G D (inr G D d)
     ≡ piinr G D d;

assert ⊢ inr nat bool true : {|sum|} nat bool; // Examples
assert ⊢ inr nat bool false : {|sum|} nat bool;
assert ⊢ {|inl_sum|} nat bool z : {|sum|} nat bool;
assert ⊢ {|inl_sum|} nat bool (succ z) : {|sum|} nat bool;

//////////////////// Vector

inductive Vec : Nat → TYPE ≔
 | nil_vec   : Vec z
 | cons_vec  : Π n, Nat → Vec n → Vec (succ n);

assert ⊢ ind_Vec : // Induction principle
 Π p, π(p z nil_vec) → (Π n x v, π(p n v) → π(p (succ n) (cons_vec n x v))) → Π n v, π(p n v);

symbol pV : Π n, Vec n → Prop; // Tests about inductive rules
symbol pinil_vec : π (pV z nil_vec);
symbol n : Nat;
symbol v : Vec n;
symbol picons_vec : Π n x v, π(pV n v) → π(pV (succ n) (cons_vec n x v));
assert ⊢ ind_Vec pV pinil_vec _ z nil_vec ≡ pinil_vec;
assert ⊢ ind_Vec pV pinil_vec picons_vec (succ n) (cons_vec n x v)
     ≡ picons_vec n x v (ind_Vec pV pinil_vec picons_vec n v);

assert ⊢ nil_vec : Vec z; // Examples
assert ⊢ cons_vec (succ z) x (cons_vec z x nil_vec) : Vec (succ (succ z));

///////////////// An example of the heterogenous dependent family

inductive fin : Nat → TYPE ≔
  | new : Π n, fin (succ n)
  | inj : Π n, fin n → fin (succ n);

assert ⊢ ind_fin : // Induction principle
  Π p, (Π n, π (p (succ n) (new n))) → (Π n f, π (p n f) → π (p (succ n) (inj n f))) → Π n f, π (p n f);

symbol pF : Π n, fin n → Prop; // Tests about inductive rules
symbol pinew : Π n, π (pF (succ n) (new n));
symbol f : fin n;
symbol piinj : Π n f, π (pF n f) → π (pF (succ n) (inj n f));
assert ⊢ ind_fin pF pinew _ (succ n) (new n) ≡ pinew n;
assert ⊢ ind_fin pF pinew piinj (succ n) (inj n f)
     ≡ piinj n f (ind_fin pF pinew piinj n f);

assert ⊢ new n : fin (succ n); // Examples
assert ⊢ inj (succ n) (new n) : fin (succ (succ n));

///////////////// Bounded List

inductive listb : τ nat → TYPE ≔
 | nilb  : Π bound, listb bound
 | consb : Π bound x, π (x ≤ bound) → listb bound → listb bound;

assert ⊢ ind_listb : // Induction principle
Π p, (Π bound, π(p bound (nilb bound))) →
(Π bound x (prf:π (x ≤ bound)) l, π(p bound l) → π(p bound (consb bound x prf l))) → 
Π bound l, π(p bound l);

symbol pbound : Π bound, listb bound → Prop; // Tests about inductive rules
symbol pinilb : Π bound, π(pbound bound (nilb bound));
symbol bound : τ nat;
symbol prf : π (x ≤ bound);
symbol lb : listb bound;
symbol piconsb : Π bound x (prf:π (x ≤ bound)) l, π(pbound bound l) → π(pbound bound (consb bound x prf l));
assert ⊢ ind_listb pbound pinilb _ bound (nilb bound) ≡ pinilb bound;
assert ⊢ ind_listb pbound pinilb piconsb bound (consb bound x prf lb)
     ≡ piconsb bound x prf lb (ind_listb pbound pinilb piconsb bound lb);

assert ⊢ nilb bound : listb bound; // Examples
assert ⊢ consb bound x prf (nilb bound) : listb bound;

///////////////// Type rom

inductive rom : Nat → TYPE ≔
 | mty : rom z // leaf node
 | bin : Π e1 e2, rom e1 → rom e2 → rom (e1 + e2 + 1)  // binary nodes
 | unl : Π e k, π (k ≤ 2 × e) → rom e → rom (succ e); // unary labeled nodes

assert ⊢ ind_rom : Π p: Π x: Nat, rom x → Prop, // Induction principle
  π (p 0 mty) →
  (Π e1: τ nat, Π e2: τ nat, Π x: rom e1, π (p e1 x) → Π x0: rom e2, π (p e2 x0) → π (p ((e1 + e2) + 1) (bin e1 e2 x x0))) → 
  (Π e: τ nat, Π k: τ nat, Π x: π (k ≤ (2 × e)), Π x0: rom e, π (p e x0) → π (p (succ e) (unl e k x x0))) → 
Π x: Nat, Π x0: rom x, π (p x x0);

symbol pRom : Π x: Nat, rom x → Prop; // Tests about inductive rules
symbol pimty : π (pRom z mty);
symbol romx : rom x;
symbol romn : rom n;
symbol pibin : Π e1: τ nat, Π e2: τ nat, Π x: rom e1,
 π (pRom e1 x) → Π x0: rom e2, π (pRom e2 x0) → π (pRom ((e1 + e2) + 1) (bin e1 e2 x x0));
symbol prf_le : π (n ≤ 2 × x);
symbol piunl : Π e: τ nat, Π k: τ nat, Π x: π (k ≤ (2 × e)), Π x0: rom e, π (pRom e x0) → π (pRom (succ e) (unl e k x x0));
assert ⊢ ind_rom pRom pimty pibin piunl _ mty ≡ pimty;
assert ⊢ ind_rom pRom pimty pibin piunl _ (unl x n prf_le romx)
     ≡ piunl x n prf_le romx (ind_rom pRom pimty pibin piunl _ romx);
assert ⊢ ind_rom pRom pimty pibin piunl _ (bin x n romx romn)
 ≡ pibin x n romx (ind_rom pRom pimty pibin piunl x romx) romn (ind_rom pRom pimty pibin piunl n romn);

assert ⊢ mty : rom z; // Examples
assert ⊢ bin z z mty mty : rom (succ z);
assert ⊢ bin z (succ z) mty (bin z z mty mty) : rom (succ (succ z));
symbol t : π (z ≤ 2 × z);
assert ⊢ bin (succ z) z (unl z z t mty) mty : rom (succ (succ z));
assert ⊢ unl z z t mty : rom (succ z);
symbol t12 : π (z ≤ 2×(succ z));
assert ⊢ unl (succ z) z t12 (bin z z mty mty) : rom (succ (succ z));

//symbol rom : Nat → TYPE
//symbol mty : rom z
//symbol bin : Π e1 e2, rom e1 → rom e2 → rom (e1+e2+1)
//symbol unl : Π e k, π (k ≤ 2×e) → rom e → rom (succ e)

//symbol ind_rom : Π p: Πx: Nat, rom x → Prop,
//  π (p 0 mty) →
//  (Π e1: τ nat, Π e2: τ nat, Π x: rom e1, π (p e1 x) → Π x0: rom e2, π (p e2 x0) → π (p ((e1 + e2) + 1) (bin e1 e2 x x0))) → 
//  (Π e: τ nat, Π k: τ nat, Π x: π (k ≤ (2 × e)), Π x0: rom e, π (p e x0) → π (p (succ e) (unl e k x x0))) → 
//Π x: Nat, Π x0: rom x, π (p x x0)

//rule ind_rom $p $pmty $pbin $punl (($x0 + $x1)+1) (bin $x0 $x1 $x2 $x3)
//   ↪ $pbin $x0 $x1 $x2 (ind_rom $p $pmty $pbin $punl $x0 $x2) $x3 (ind_rom $p $pmty $pbin $punl $x1 $x3)

/////////////////// Polymorphic vector

inductive Vec_param : Set → Nat → TYPE ≔
 | nil_vec_p   : Π a, Vec_param a z
 | cons_vec_p  : Π a n (_:τ a), Vec_param a n → Vec_param a (succ n);

assert ⊢ ind_Vec_param : // Induction principle
  Π p, (Π a, π(p a z (nil_vec_p a))) → (Π a n x v, π(p a n v) → π(p a (succ n) (cons_vec_p a n x v))) → Π a n v, π(p a n v);

symbol pV_p : Π a n, Vec_param a n → Prop; // Tests about inductive rules
symbol pinil_vec_p : Π a, π (pV_p a z (nil_vec_p a));
symbol xV_p : τ a;
symbol v_p : Vec_param a n;
symbol picons_vec_p : Π a n x v, π(pV_p a n v) → π(pV_p a (succ n) (cons_vec_p a n x v));
assert ⊢ ind_Vec_param pV_p pinil_vec_p _ a z (nil_vec_p a) ≡ pinil_vec_p a;
assert ⊢ ind_Vec_param pV_p pinil_vec_p picons_vec_p a (succ n) (cons_vec_p a n xV_p v_p)
     ≡ picons_vec_p a n xV_p v_p (ind_Vec_param pV_p pinil_vec_p picons_vec_p a n v_p);

assert ⊢ nil_vec_p a : Vec_param a z; // Examples
assert ⊢ nil_vec_p nat : Vec_param nat z;
assert ⊢ cons_vec_p nat (succ z) (succ (succ (succ z))) (cons_vec_p nat z z (nil_vec_p nat)) : Vec_param nat (succ (succ z));
assertnot ⊢ cons_vec_p nat (succ z) (succ (succ (succ z))) (cons_vec_p nat z true (nil_vec_p nat)) : Vec_param nat (succ (succ z));
assert ⊢ cons_vec_p bool (succ z) false (cons_vec_p bool z true (nil_vec_p bool)) : Vec_param bool (succ (succ z));

////////////////// Type Bush (nested inductive type)

symbol bush : Set →  Set;
inductive Bush : Π(_:Set), TYPE ≔
 | bnil : Π a, Bush a
 | bcons : Π a, τ a → Bush (bush a) → Bush a;
rule Bush $a ↪ τ (bush $a);

assert ⊢ ind_Bush : // Induction principle
  Π p, (Π a, π(p a (bnil a))) → (Π a x l, π(p (bush a) l) → π(p a (bcons a x l))) → Π a l, π(p a l);

symbol pB : Π a, Bush a → Prop; // Tests about inductive rules
symbol pibnil : Π a, π (pB a (bnil a));
symbol B : Bush (bush a);
symbol pibcons : Π a x l, π (pB (bush a) l) → π (pB a (bcons a x l));
assert ⊢ ind_Bush pB pibnil _ a (bnil a) ≡ pibnil a;
assert ⊢ ind_Bush pB pibnil pibcons a (bcons a xa B)
     ≡ pibcons a xa B (ind_Bush pB pibnil pibcons (bush a) B);

assert ⊢ bnil a : Bush a; // Examples
assert ⊢ bcons nat (succ (succ (succ z))) (bnil (bush nat)) : Bush nat;
//assert bcons nat (succ (succ (succ z))) (bcons (bush nat) (τ (bush nat)) (bnil (bush (bush nat)))) : Bush nat;
//assert bcons nat (succ (succ (succ z))) (bcons nat (succ z) (bcons nat z (bnil nat))) : Bush nat;
assert ⊢ bcons bool true (bnil (bush bool)) : Bush bool;

/////////////////////////////
// Some ≔ begins
/////////////////////////////

opaque symbol plus_0_n : Π n, π ((0 + n) = n)
≔ begin
  assume n;
  reflexivity;
end

opaque symbol plus_n_0 : Π n, π ((n + 0) = n)
≔ begin
  assume n;
  refine ind_Nat (λ z, (z + 0) = z) _ _ _;
  // Case n = O
  refine eq_refl 0;
  // Case n = S n'
  assume n' Hn';
  simpl;
  rewrite Hn';
  reflexivity;
end

// About lists
symbol length : List → Nat;
rule length nil ↪ 0
 with length (cons _ $l) ↪ succ (length $l);

symbol app : List → List → List;
rule  app      nil     $m ↪ $m
 with app (cons $x $l) $m ↪ cons $x (app $l $m);

opaque symbol length_app :
  Π(l1 l2 : List), π ((length l1 + length l2) = length (app l1 l2))
≔ begin
  assume l1 l2;
  apply ind_List
        (λ z, (length z + length l2) = length (app z l2)) _ _ l1;
  reflexivity;
  assume x l2 IHl1;
  simpl; rewrite IHl1; reflexivity;
end
