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

////////////////// Primary color

inductive RGB : TYPE ≔
 | red  : RGB
 | green : RGB
 | blue : RGB

assert RGB : TYPE
assert red : RGB
assert green : RGB
assert blue : RGB

assert ind_RGB :
  Πp : RGB → Prop,
  π (p red) → π (p green) → π (p blue) →
  Πx, π (p x)

symbol pRGB : RGB → Prop
symbol pred : π (pRGB red)
symbol pgreen : π (pRGB green)
symbol pblue: π (pRGB blue)
symbol indRGB ≔ ind_RGB pRGB pred pgreen pblue
assert indRGB red ≡ pred
assert indRGB green ≡ pgreen
assert indRGB blue ≡ pblue

////////////////// Type color

inductive Color : TYPE ≔
 | black : Color
 | white : Color
 | primary : RGB → Color

assert Color : TYPE
assert white : Color
assert black : Color
assert primary : RGB → Color

assert ind_Color :
  Πp : Color → Prop,
  π (p black) → π (p white) → (Πx, π (p (primary x))) →
  Πx, π (p x)

symbol pColor : Color → Prop
symbol pblack : π (pColor black)
symbol pwhite : π (pColor white)
symbol pprimary: Πx, π (pColor (primary x))
symbol indColor ≔ ind_Color pColor pblack pwhite pprimary
assert indColor black ≡ pblack
assert indColor white ≡ pwhite
symbol rgb : RGB
assert indColor (primary rgb) ≡ pprimary rgb

////////////////// Boolean type

//FIXME:
//set declared "𝔹"
//inductive 𝔹 : TYPE ≔
// | true  : 𝔹
// | false : 𝔹
// identifier ind_𝔹 not recognized

inductive B : TYPE ≔
 | true  : B
 | false : B

assert B: TYPE
assert true  : B
assert false : B

assert ind_B :
  Πp : B → Prop,
  π (p true) → π (p false) →
  Πb, π (p b)

symbol pBool : B → Prop
symbol pitrue  : π (pBool true)
symbol pifalse : π (pBool false)
symbol indBool ≔ ind_B pBool pitrue pifalse
assert indBool true  ≡ pitrue
assert indBool false ≡ pifalse

constant symbol bool : Set
rule B ↪ τ bool

////////////////// False (not predicate one)

inductive False : TYPE ≔

assert False : TYPE
assert ind_False : Π(p:False → Prop) (f : False), π (p f)

///////////////// Natural number

inductive N : TYPE ≔
 | z    : N
 | succ : N → N

assert N : TYPE
assert z : N
assert succ : N → N

assert ind_N :
  Πp:N → Prop, π(p z) → (Πx, π (p x) → π (p (succ x))) → Πx, π (p x)

symbol pN : N → Prop
symbol pz : π (pN z)
symbol psucc : Πx, π (pN x) → π (pN (succ x))
symbol indN ≔ ind_N pN pz psucc
assert indN z ≡ pz
symbol n : N
assert indN (succ n) ≡ psucc n (indN n)

constant symbol nat : Set
rule N ↪ τ nat

// About natural numbers
set builtin "0"  ≔ z
set builtin "+1" ≔ succ

symbol plus : N → N → N
set infix left 6 "+" ≔ plus
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y)

symbol mult : N → N → N
set infix left 7 "×" ≔ mult
rule       0 × _  ↪ 0
with succ $x × $y ↪ $y + $x × $y

symbol le : N → N → Prop
set infix left 6 "≤" ≔ le
//inductive ≤ : Π(n:τ nat), N → Prop ≔
//  | le_n : Πn, π (n ≤ n)
//  | le_S : Πn m:τ nat, π (n ≤ m) → π (n ≤ (succ m))

/////////////////// Arithmetic and boolean expressions

inductive Expr : TYPE ≔
 | Lit : N → Expr
 | Add : Expr → Expr → Expr
 | If  : BExpr → Expr → Expr → Expr
with BExpr : TYPE ≔
 | BLit : B → BExpr
 | And  : BExpr → BExpr → BExpr
 | Not  : BExpr → BExpr
 | Equal  : Expr → Expr → BExpr

assert Expr : TYPE
assert Lit : N → Expr
assert Add : Expr → Expr → Expr
assert If  : BExpr → Expr → Expr → Expr
assert BExpr : TYPE
assert BLit : B → BExpr
assert And  : BExpr → BExpr → BExpr
assert Not  : BExpr → BExpr
assert Equal  : Expr → Expr → BExpr

assert ind_Expr :
  Πp0: Expr → Prop, Πp1: BExpr → Prop,
    (Πx: N, π (p0 (Lit x))) →
    (Πx: Expr, π (p0 x) → Πx0: Expr, π (p0 x0) → π (p0 (Add x x0))) →
    (Πx: BExpr, π (p1 x) → Πx0: Expr, π (p0 x0) → Πx1: Expr, π (p0 x1) → π (p0 (If x x0 x1))) → 
    (Πx: B, π (p1 (BLit x))) →
    (Πx: BExpr, π (p1 x) → Πx0: BExpr, π (p1 x0) → π (p1 (And x x0))) →
    (Πx: BExpr, π (p1 x) → π (p1 (Not x))) →
    (Πx: Expr, π (p0 x) → Πx0: Expr, π (p0 x0) → π (p1 (Equal x x0))) →
  Πx: Expr, π (p0 x)

assert ind_BExpr :
  Πp0: Expr → Prop, Πp1: BExpr → Prop,
    (Πx: N, π (p0 (Lit x))) →
    (Πx: Expr, π (p0 x) → Πx0: Expr, π (p0 x0) → π (p0 (Add x x0))) →
    (Πx: BExpr, π (p1 x) → Πx0: Expr, π (p0 x0) → Πx1: Expr, π (p0 x1) → π (p0 (If x x0 x1))) →
    (Πx: B, π (p1 (BLit x))) →
    (Πx: BExpr, π (p1 x) → Πx0: BExpr, π (p1 x0) → π (p1 (And x x0))) →
    (Πx: BExpr, π (p1 x) → π (p1 (Not x))) →
    (Πx: Expr, π (p0 x) → Πx0: Expr, π (p0 x0) → π (p1 (Equal x x0))) →
  Πx: BExpr, π (p1 x)

symbol p0 : Expr → Prop
symbol p1 : BExpr → Prop
symbol pLit : Πx: N, π (p0 (Lit x))
symbol pAdd : Πx: Expr, π (p0 x) → Πx0: Expr, π (p0 x0) → π (p0 (Add x x0))
symbol pIf : Πx: BExpr, π (p1 x) → Πx0: Expr, π (p0 x0) → Πx1: Expr, π (p0 x1) → π (p0 (If x x0 x1))
symbol pBLit : Πx: B, π (p1 (BLit x))
symbol pAnd : Πx: BExpr, π (p1 x) → Πx0: BExpr, π (p1 x0) → π (p1 (And x x0))
symbol pNot : Πx: BExpr, π (p1 x) → π (p1 (Not x))
symbol pEqual : Πx: Expr, π (p0 x) → Πx0: Expr, π (p0 x0) → π (p1 (Equal x x0))
symbol indE ≔ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
symbol indBE ≔ ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
symbol x : B
symbol e1 : Expr
symbol e2 : Expr
symbol be1 : BExpr
symbol be2 : BExpr
assert indE (Lit n) ≡ pLit n
assert indE (Add e1 e2) ≡ pAdd e1 (indE e1) e2 (indE e2)
assert indE (If be1 e1 e2) ≡ pIf be1 (indBE be1) e1 (indE e1) e2 (indE e2)
assert indBE (BLit x) ≡ pBLit x
assert indBE (And be1 be2) ≡ pAnd be1 (indBE be1) be2 (indBE be2)
assert indBE (Not be1) ≡ pNot be1 (indBE be1)
assert indBE (Equal e1 e2) ≡ pEqual e1 (indE e1) e2 (indE e2)

/////////////////// Arithmetic and boolean expressions, and commands

inductive AExp : TYPE ≔
 | aLit : N → AExp
 | aAdd : AExp → AExp → AExp
 | aIf  : BExp → AExp → AExp → AExp
with BExp : TYPE ≔
 | bLit : B → BExp
 | bEq : AExp → AExp → BExp
with CExp : TYPE ≔
 | cSkip : CExp
 | cAss  : Set → AExp → CExp // FIXME: What is Set here ?
 | cSeq  : CExp → CExp → CExp
 | cIf   : BExp → CExp → CExp → CExp

assert AExp : TYPE
assert aLit : N → AExp
assert aAdd : AExp → AExp → AExp
assert aIf  : BExp → AExp → AExp → AExp
assert BExp : TYPE
assert bLit : B → BExp
assert bEq : AExp → AExp → BExp
assert CExp : TYPE
assert cSkip : CExp
assert cAss  : Set → AExp → CExp
assert cSeq  : CExp → CExp → CExp
assert cIf   : BExp → CExp → CExp → CExp

assert ind_AExp :
  ΠpA: AExp → Prop, ΠpB: BExp → Prop, ΠpC: CExp → Prop,
   (Πx: N, π (pA (aLit x))) →
   (Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pA (aAdd x x0))) →
   (Πx: BExp, π (pB x) → Πx0: AExp, π (pA x0) → Πx1: AExp, π (pA x1) → π (pA (aIf x x0 x1))) →
   (Πx: B, π (pB (bLit x))) →
   (Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pB (bEq x x0))) →
   π (pC cSkip) →
   (Πx: Set, Πx0: AExp, π (pA x0) → π (pC (cAss x x0))) →
   (Πx: CExp, π (pC x) → Πx0: CExp, π (pC x0) → π (pC (cSeq x x0))) →
   (Πx: BExp, π (pB x) → Πx0: CExp, π (pC x0) → Πx1: CExp, π (pC x1) → π (pC (cIf x x0 x1))) →
  Πx: AExp, π (pA x)

assert ind_BExp :
  ΠpA: AExp → Prop, ΠpB: BExp → Prop, ΠpC: CExp → Prop,
   (Πx: N, π (pA (aLit x))) →
   (Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pA (aAdd x x0))) →
   (Πx: BExp, π (pB x) → Πx0: AExp, π (pA x0) → Πx1: AExp, π (pA x1) → π (pA (aIf x x0 x1))) →
   (Πx: B, π (pB (bLit x))) →
   (Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pB (bEq x x0))) →
   π (pC cSkip) →
   (Πx: Set, Πx0: AExp, π (pA x0) → π (pC (cAss x x0))) →
   (Πx: CExp, π (pC x) → Πx0: CExp, π (pC x0) → π (pC (cSeq x x0))) →
   (Πx: BExp, π (pB x) → Πx0: CExp, π (pC x0) → Πx1: CExp, π (pC x1) → π (pC (cIf x x0 x1))) →
  Πx: BExp, π (pB x)

assert ind_CExp :
  ΠpA: AExp → Prop, ΠpB: BExp → Prop, ΠpC: CExp → Prop,
   (Πx: N, π (pA (aLit x))) →
   (Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pA (aAdd x x0))) →
   (Πx: BExp, π (pB x) → Πx0: AExp, π (pA x0) → Πx1: AExp, π (pA x1) → π (pA (aIf x x0 x1))) →
   (Πx: B, π (pB (bLit x))) →
   (Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pB (bEq x x0))) →
   π (pC cSkip) →
   (Πx: Set, Πx0: AExp, π (pA x0) → π (pC (cAss x x0))) →
   (Πx: CExp, π (pC x) → Πx0: CExp, π (pC x0) → π (pC (cSeq x x0))) →
   (Πx: BExp, π (pB x) → Πx0: CExp, π (pC x0) → Πx1: CExp, π (pC x1) → π (pC (cIf x x0 x1))) →
  Πx: CExp, π (pC x)

symbol pA : AExp → Prop
symbol pB : BExp → Prop
symbol pC : CExp → Prop
symbol paLit : Πx: N, π (pA (aLit x))
symbol paAdd : Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pA (aAdd x x0))
symbol paIf : Πx: BExp, π (pB x) → Πx0: AExp, π (pA x0) → Πx1: AExp, π (pA x1) → π (pA (aIf x x0 x1))
symbol pbLit : Πx: B, π (pB (bLit x))
symbol pbEq :Πx: AExp, π (pA x) → Πx0: AExp, π (pA x0) → π (pB (bEq x x0))
symbol pcSkip : π (pC cSkip)
symbol pcAss : Πx: Set, Πx0: AExp, π (pA x0) → π (pC (cAss x x0))
symbol pcSeq : Πx: CExp, π (pC x) → Πx0: CExp, π (pC x0) → π (pC (cSeq x x0))
symbol pcIf : Πx: BExp, π (pB x) → Πx0: CExp, π (pC x0) → Πx1: CExp, π (pC x1) → π (pC (cIf x x0 x1))
symbol indA ≔ ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
symbol indB ≔ ind_BExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
symbol indC ≔ ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
symbol a1 : AExp
symbol a2 : AExp
symbol b : BExp
symbol c1 : CExp
symbol c2 : CExp
symbol s : Set
assert indA (aLit n) ≡ paLit n
assert indA (aAdd a1 a2) ≡ paAdd a1 (indA a1) a2 (indA a2)
assert indA (aIf b a1 a2) ≡ paIf b (indB b) a1 (indA a1) a2 (indA a2)
assert indB (bLit x) ≡ pbLit x
assert indB (bEq a1 a2) ≡ pbEq a1 (indA a1) a2 (indA a2)
assert indC cSkip ≡ pcSkip
assert indC (cAss s a1) ≡ pcAss s a1 (indA a1)
assert indC (cSeq c1 c2) ≡ pcSeq c1 (indC c1) c2 (indC c2)
assert indC (cIf b c1 c2) ≡ pcIf b (indB b) c1 (indC c1) c2 (indC c2)

////////////////////// Even and odd

inductive even : N → TYPE ≔
  | even_O : even 0
  | even_S : Πn, odd n → even (succ n)
with odd : N → TYPE ≔
  | odd_S : Πn, even n → odd (succ n)

assert even : N → TYPE
assert even_O : even 0
assert even_S : Πn, odd n → even (succ n)
assert odd : N → TYPE
assert odd_S : Πn, even n → odd (succ n)

assert ind_even :
  Πp0: Πx: N, even x → Prop, Πp1: Πx: N, odd x → Prop,
    π (p0 0 even_O) →
   (Πn: τ nat, Πx: odd n, π (p1 n x) → π (p0 (succ n) (even_S n x))) →
   (Πn: τ nat, Πx: even n, π (p0 n x) → π (p1 (succ n) (odd_S n x))) →
  Πx: N, Πx0: even x, π (p0 x x0)

assert ind_odd :
  Πp0: Πx: N, even x → Prop, Πp1: Πx: N, odd x → Prop,
    π (p0 0 even_O) →
    (Πn: τ nat, Πx: odd n, π (p1 n x) → π (p0 (succ n) (even_S n x))) →
    (Πn: τ nat, Πx: even n, π (p0 n x) → π (p1 (succ n) (odd_S n x))) →
  Πx: N, Πx0: odd x, π (p1 x x0)

symbol podd : Πx: N, odd x → Prop
symbol peven : Πx: N, even x → Prop
symbol peven_O : π (peven z even_O)
symbol peven_S : Πn: τ nat, Πx: odd n, π (podd n x) → π (peven (succ n) (even_S n x))
symbol podd_S : Πn: τ nat, Πx: even n, π (peven n x) → π (podd (succ n) (odd_S n x))
symbol indodd ≔ ind_odd peven podd peven_O peven_S podd_S
symbol indeven ≔ ind_even peven podd peven_O peven_S podd_S
symbol evenn : even n
symbol oddn : odd n
assert indodd _ (odd_S n evenn) ≡ podd_S n evenn (indeven _ evenn)
assert indeven _ even_O ≡ peven_O
assert indeven _ (even_S n oddn) ≡ peven_S n oddn (indodd _ oddn)

////////////////////// List of natural numbers

inductive List : TYPE ≔
 | nil  : List
 | cons : N → List → List

assert List : TYPE
assert nil  : List
assert cons : N → List → List

assert ind_List :
  Π(p:List → Prop), π(p nil) → (Πx l,π(p l) → π(p(cons x l))) → Πl,π(p l)

symbol pL : List → Prop
symbol pnil : π (pL nil)
symbol pcons : Πx l, π (pL l) → π (pL (cons x l))
symbol indL ≔ ind_List pL pnil pcons
symbol l : List
assert indL nil ≡ pnil
assert indL (cons n l) ≡ pcons n l (indL l)

constant symbol list : Set
rule List ↪ τ list

///////////////// Couple of natural numbers

inductive nat_prod : TYPE ≔
 | prod : N → N → nat_prod

assert nat_prod : TYPE
assert prod : N → N → nat_prod

assert ind_nat_prod :
Πp : nat_prod → Prop,
(Πx0 x1, π (p (prod x0 x1))) →
Πx, π (p x)

symbol pNP : nat_prod → Prop
symbol pprod : Πx0 x1, π (pNP (prod x0 x1))
symbol indNP ≔ ind_nat_prod pNP pprod
symbol n1 : N
symbol n2 : N
assert indNP (prod n1 n2) ≡ pprod n1 n2

///////////////// Binary tree

inductive Tree : TYPE ≔
  | leaf : Tree
  | consTree : Tree → N → Tree → Tree

assert Tree : TYPE
assert leaf : Tree
assert consTree : Tree → N → Tree → Tree

assert ind_Tree : Πp,
π (p leaf) →
(Πt1, π (p t1) → Πx t2, π (p t2) → π (p (consTree t1 x t2))) →
Πt, π (p t)

symbol pT : Tree → Prop
symbol pleaf : π (pT leaf)
symbol pconsTree : Πt1, π (pT t1) → Πx t2, π (pT t2) → π (pT (consTree t1 x t2))
symbol t1 : Tree
symbol t2 : Tree
symbol indT ≔ ind_Tree pT pleaf pconsTree
assert indT leaf ≡ pleaf
assert indT (consTree t1 n t2) ≡ pconsTree t1 (indT t1) n t2 (indT t2)

///////////////////// Polymorphic list

inductive L (a:Set) : TYPE ≔
 | nilL  : L a
 | consL : τ a → L a → L a

assert L : Set → TYPE
assert nilL  : Πa, L a
assert consL : Πa, τ a → L a → L a

assert ind_L :
  Πp, (Πa, π(p a (nilL a))) → (Πa x l, π(p a l) → π(p a (consL a x l))) → Πa l, π(p a l)

symbol pList : Πa, L a → Prop
symbol pnilL : Πa, π (pList a (nilL a))
symbol pconsL : Πa x l, π (pList a l) → π (pList a (consL a x l))
symbol indList ≔ ind_L pList pnilL pconsL
symbol a : Set
symbol xa : τ a
symbol la : L a
assert indList a (nilL a) ≡ pnilL a
assert indList a (consL a xa la) ≡ pconsL a xa la (indList a la)

////////////////// Type sum - test names between {|...|} too

inductive {|sum|} : Set → Set → TYPE ≔
 | {|inl_sum|} : Πa b, τ a → {|sum|} a b
 | inr : Πa b, τ b → {|sum|} a b

assert {|sum|} : Set → Set → TYPE
assert {|inl_sum|} : Πa b, τ a → {|sum|} a b
assert inr : Πa b, τ b → {|sum|} a b

assert {|ind_sum|} : Πp,
(Πa b xa, π (p a b ({|inl_sum|} a b xa))) →
(Πa b xb, π (p a b (inr a b xb))) →
Πa b s, π (p a b s)

symbol pS : Π(a:Set) (b:Set), {|sum|} a b → Prop
symbol pinl : Πa b xa, π (pS a b ({|inl_sum|} a b xa))
symbol pinr : Πa b xb, π (pS a b (inr a b xb))
symbol g : Set
symbol xg : τ g
symbol d : Set
symbol xd : τ d
symbol indsum ≔ {|ind_sum|} pS pinl pinr
assert indsum g d ({|inl_sum|} g d xg) ≡ pinl g d xg
assert indsum g d (inr g d xd) ≡ pinr g d xd

//////////////////// Vector

inductive V : N → TYPE ≔
 | nil_vec   : V z
 | cons_vec  : Πn, N → V n → V (succ n)

assert V : N → TYPE
assert nil_vec   : V z
assert cons_vec  : Πn, N → V n → V (succ n)

assert ind_V :
 Πp, π(p z nil_vec) → (Πn x v, π(p n v) → π(p (succ n) (cons_vec n x v))) → Πn v, π(p n v)

symbol pV : Πn, V n → Prop
symbol pVnil : π (pV z nil_vec)
symbol pVcons : Πn x v, π(pV n v) → π(pV (succ n) (cons_vec n x v))
symbol indV ≔ ind_V pV pVnil pVcons
symbol v : V n
symbol y : N
assert indV z nil_vec ≡ pVnil
assert indV (succ n) (cons_vec n y v) ≡ pVcons n y v (indV n v)

///////////////// An example of heterogenous dependent family

inductive fin : N → TYPE ≔
  | new : Πn, fin (succ n)
  | inj : Πn, fin n → fin (succ n)

assert fin : N → TYPE
assert new : Πn, fin (succ n)
assert inj : Πn, fin n → fin (succ n)

assert ind_fin :
  Πp, (Πn, π (p (succ n) (new n))) → (Πn f, π (p n f) → π (p (succ n) (inj n f))) → Πn f, π (p n f)

symbol pF : Πn, fin n → Prop
symbol pnew : Πn, π (pF (succ n) (new n))
symbol pinj : Πn f, π (pF n f) → π (pF (succ n) (inj n f))
symbol indF ≔ ind_fin pF pnew pinj
symbol f : fin n
assert indF (succ n) (new n) ≡ pnew n
assert indF (succ n) (inj n f) ≡ pinj n f (indF n f)

///////////////// Bounded List

inductive listb : τ nat → TYPE ≔
 | nilb  : Πbound, listb bound
 | consb : Πbound x, π (x ≤ bound) → listb bound → listb bound

assert listb : τ nat → TYPE
assert nilb  : Πbound, listb bound
assert consb : Πbound x, π (x ≤ bound) → listb bound → listb bound

assert ind_listb :
Πp, (Πbound, π(p bound (nilb bound))) →
(Πbound x (prf:π (x ≤ bound)) l, π(p bound l) → π(p bound (consb bound x prf l))) → 
Πbound l, π(p bound l)

symbol pbound : Πbound, listb bound → Prop
symbol pnilb : Πbound, π(pbound bound (nilb bound))
symbol pconsb : Πbound x (prf:π (x ≤ bound)) l, π(pbound bound l) → π(pbound bound (consb bound x prf l))
symbol indb ≔ ind_listb pbound pnilb pconsb
symbol prf : π (y ≤ n)
symbol lb : listb n
assert indb n (nilb n) ≡ pnilb n
assert indb n (consb n y prf lb) ≡ pconsb n y prf lb (indb n lb)

///////////////// Type rom

inductive rom : N → TYPE ≔
 | mty : rom z // leaf node
 | bin : Πe1 e2, rom e1 → rom e2 → rom (e1+e2+1)  // binary nodes
 | unl : Πe k, π (k ≤ 2×e) → rom e → rom (succ e) // unary labeled nodes

assert rom : N → TYPE
assert mty : rom z
assert bin : Πe1 e2, rom e1 → rom e2 → rom (e1+e2+1)
assert unl : Πe k, π (k ≤ 2×e) → rom e → rom (succ e)

assert ind_rom : Πp: Πx: N, rom x → Prop,
  π (p 0 mty) →
  (Πe1: τ nat, Πe2: τ nat, Πx: rom e1, π (p e1 x) → Πx0: rom e2, π (p e2 x0) → π (p ((e1 + e2) + 1) (bin e1 e2 x x0))) → 
  (Πe: τ nat, Πk: τ nat, Πx: π (k ≤ (2 × e)), Πx0: rom e, π (p e x0) → π (p (succ e) (unl e k x x0))) → 
Πx: N, Πx0: rom x, π (p x x0)

symbol pRom : Πx: N, rom x → Prop
symbol pmty : π (pRom z mty)
symbol pbin : Πe1: τ nat, Πe2: τ nat, Πx: rom e1,
 π (pRom e1 x) → Πx0: rom e2, π (pRom e2 x0) → π (pRom ((e1 + e2) + 1) (bin e1 e2 x x0))
symbol punl : Πe: τ nat, Πk: τ nat, Πx: π (k ≤ (2 × e)), Πx0: rom e, π (pRom e x0) → π (pRom (succ e) (unl e k x x0))
symbol indr ≔ ind_rom pRom pmty pbin punl
symbol prf_le : π (n ≤ 2×y)
symbol romy : rom y
symbol romn : rom n
assert indr _ mty ≡ pmty
assert indr _ (unl y n prf_le romy) ≡ punl y n prf_le romy (indr _ romy)
assert indr _ (bin y n romy romn) ≡ pbin y n romy (indr y romy) romn (indr n romn)

///////////////// Fibonacci suite

inductive fibo : N → N → TYPE ≔
 | cgen' : Π (n r1 r2 : N),
    fibo n r1 → fibo (succ n) r2 →  fibo (succ (succ n)) (plus r1 r2)
 | cbase1 : fibo z (succ z)
 | cbase2 : fibo (succ z) (succ z)

assert fibo : N → N → TYPE
assert cgen' : Π (n r1 r2 : N),
    fibo n r1 → fibo (succ n) r2 →  fibo (succ (succ n)) (plus r1 r2)
assert cbase1 : fibo z (succ z)
assert cbase2 : fibo (succ z) (succ z)

assert ind_fibo : Πp: Πx: N, Πx0: N, fibo x x0 → Prop,
(Πn r1 r2,
     Πx0: fibo n r1, π (p n r1 x0) →
     Πx1: fibo (succ n) r2, π (p (succ n) r2 x1) →
π (p (succ (succ n)) (r1 + r2) (cgen' n r1 r2 x0 x1))) →
π (p 0 1 cbase1) →
π (p 1 1 cbase2) →
Πx: N, Πx0: N, Πx1: fibo x x0, π (p x x0 x1)

symbol pFibo : Πx: N, Πx0: N, fibo x x0 → Prop
symbol pcgen' : (Πn r1 r2, Πx0: fibo n r1, π (pFibo n r1 x0) → Πx1: fibo (succ n) r2,
                  π (pFibo (succ n) r2 x1) → π (pFibo (succ (succ n)) (r1 + r2) (cgen' n r1 r2 x0 x1)))
symbol pcbase1 : π (pFibo 0 1 cbase1)
symbol pcbase2 : π (pFibo 1 1 cbase2)
symbol indfibo ≔ ind_fibo pFibo pcgen' pcbase1 pcbase2
symbol r1 : N
symbol r2 : N
symbol hypF1 : fibo n r1
symbol hypF2 : fibo (succ n) r2
assert indfibo _ _ (cgen' n r1 r2 hypF1 hypF2)
     ≡ pcgen' n r1 r2 hypF1 (indfibo _ _ hypF1) 
                      hypF2 (indfibo _ _ hypF2)
assert indfibo _ _ cbase1 ≡ pcbase1
assert indfibo _ _ cbase2 ≡ pcbase2

/////////////////// Polymorphic vector

inductive Vec : Set → N → TYPE ≔
 | Vnil   : Πa, Vec a z
 | Vcons  : Πa n (_:τ a), Vec a n → Vec a (succ n)

assert Vec : Set → N → TYPE
assert Vnil   : Πa, Vec a z
assert Vcons  : Πa n (_:τ a), Vec a n → Vec a (succ n)

assert ind_Vec :
  Πp, (Πa, π(p a z (Vnil a))) → (Πa n x v, π(p a n v) → π(p a (succ n) (Vcons a n x v))) → Πa n v, π(p a n v)

symbol pVec : Πa n, Vec a n → Prop
symbol pVecnil : Πa, π (pVec a z (Vnil a))
symbol pVeccons : Πa n x v, π(pVec a n v) → π(pVec a (succ n) (Vcons a n x v))
symbol indVec ≔ ind_Vec pVec pVecnil pVeccons
symbol xV_p : τ a
symbol v_p : Vec a n
assert ind_Vec pVec pVecnil _ a z (Vnil a) ≡ pVecnil a
assert indVec a (succ n) (Vcons a n xV_p v_p)
     ≡ pVeccons a n xV_p v_p (indVec a n v_p)

////////////////// Type Bush (nested inductive type)

symbol bush : Set →  Set

inductive Bush : Π(_:Set), TYPE ≔
 | bnil : Πa, Bush a
 | bcons : Πa, τ a → Bush (bush a) → Bush a

rule Bush $a ↪ τ (bush $a)

assert Bush : Π(_:Set), TYPE
assert bnil : Πa, Bush a
assert bcons : Πa, τ a → Bush (bush a) → Bush a

assert ind_Bush :
  Πp, (Πa, π(p a (bnil a))) → (Πa x l, π(p (bush a) l) → π(p a (bcons a x l))) → Πa l, π(p a l)

symbol pBush : Πa, Bush a → Prop
symbol pbnil : Πa, π (pBush a (bnil a))
symbol pbcons : Πa x l, π (pBush (bush a) l) → π (pBush a (bcons a x l))
symbol indbush ≔ ind_Bush pBush pbnil pbcons
symbol tb : Bush (bush a)
assert indbush a (bnil a) ≡ pbnil a
assert indbush a (bcons a xa tb) ≡ pbcons a xa tb (indbush (bush a) tb)

/////////////////////////////
// Some begins
/////////////////////////////

opaque symbol plus_0_n : Πn, π ((0 + n) = n) ≔
begin
  assume n
  reflexivity
end

opaque symbol plus_n_0 : Πn, π ((n + 0) = n) ≔
begin
  assume n
  refine ind_N (λz, (z + 0) = z) _ _ _
  // Case n = O
  refine eq_refl 0
  // Case n = S n'
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
end

// About lists
symbol length : List → N
rule length nil ↪ 0
 with length (cons _ $l) ↪ succ (length $l)

symbol app : List → List → List
rule  app      nil     $m ↪ $m
 with app (cons $x $l) $m ↪ cons $x (app $l $m)

opaque symbol length_app :
  Π(l1 l2 : List), π ((length l1 + length l2) = length (app l1 l2)) ≔
begin
  assume l1 l2
  apply ind_List
        (λz, (length z+length l2) = length (app z l2)) _ _ l1
  reflexivity
  assume x l2 IHl1
  simpl rewrite IHl1 reflexivity
end
