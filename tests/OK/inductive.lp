/////////////////////////////
// Some examples of inductive types
/////////////////////////////

// Configuration

constant symbol Prop : TYPE;      // Type of propositions
builtin "Prop" ≔ Prop;

injective symbol π : Prop → TYPE; // Interpretation of propositions in TYPE
builtin "P" ≔ π;

constant symbol Set : TYPE;       // Type of set codes
injective symbol τ : Set → TYPE;  // Interpretation of set codes in TYPE

/// test escaped type
inductive {| |}:TYPE ≔ c : {| |};
assert ⊢ {|ind_ |} : Π p:{| |} → Prop, π (p c) → Π x: {| |}, π (p x);

////////////////// Primary colors

inductive RGB : TYPE ≔
 | red  : RGB
 | green : RGB
 | blue : RGB;

assert ⊢ RGB : TYPE;
assert ⊢ red : RGB;
assert ⊢ green : RGB;
assert ⊢ blue : RGB;

assert ⊢ ind_RGB :
  Π p : RGB → Prop,
  π(p red) → π(p green) → π(p blue) →
  Π x, π(p x);

assert p pred pgreen pblue ⊢ ind_RGB p pred pgreen pblue red ≡ pred;
assert p pred pgreen pblue ⊢ ind_RGB p pred pgreen pblue green ≡ pgreen;
assert p pred pgreen pblue ⊢ ind_RGB p pred pgreen pblue blue ≡ pblue;

////////////////// More colors

inductive Color : TYPE ≔
 | black : Color
 | white : Color
 | primary : RGB → Color;

assert ⊢ Color : TYPE;
assert ⊢ white : Color;
assert ⊢ black : Color;
assert ⊢ primary : RGB → Color;

assert ⊢ ind_Color :
  Π p : Color → Prop,
  π(p black) → π(p white) → (Π x, π(p (primary x))) →
  Π x, π(p x);

assert pColor pblack pwhite pprimary
⊢ ind_Color pColor pblack pwhite pprimary black ≡ pblack;
assert pColor pblack pwhite pprimary
⊢ ind_Color pColor pblack pwhite pprimary white ≡ pwhite;
assert pColor pblack pwhite pprimary rgb
⊢ ind_Color pColor pblack pwhite pprimary (primary rgb) ≡ pprimary rgb;

////////////////// Boolean type

inductive B : TYPE ≔
 | true  : B
 | false : B;

assert ⊢ B: TYPE;
assert ⊢ true  : B;
assert ⊢ false : B;

assert ⊢ ind_B :
  Π p : B → Prop,
  π(p true) → π(p false) →
  Π b, π(p b);

assert p ptrue pfalse ⊢ ind_B p ptrue pfalse true ≡ ptrue;
assert p ptrue pfalse ⊢ ind_B p ptrue pfalse false ≡ pfalse;

constant symbol bool : Set;
rule τ bool ↪ B;

////////////////// False (empty type)

inductive False : TYPE ≔ /* no constructor */ ;

assert ⊢ False : TYPE;
assert ⊢ ind_False : Π(p:False → Prop) (f : False), π(p f);

///////////////// Natural numbers

inductive N : TYPE ≔
 | z    : N
 | succ : N → N;

assert ⊢ N : TYPE;
assert ⊢ z : N;
assert ⊢ succ : N → N;

assert ⊢ ind_N :
  Π p:N → Prop, π(p z) → (Π x, π(p x) → π(p (succ x))) → Π x, π(p x);

assert p pz psucc ⊢ ind_N p pz psucc z ≡ pz;
assert p pz psucc n ⊢ ind_N p pz psucc (succ n) ≡ psucc n (ind_N p pz psucc n);

constant symbol nat : Set;
rule τ nat ↪ N;

builtin "0"  ≔ z;
builtin "+1" ≔ succ;

symbol + : N → N → N;
notation + infix left 6;
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y);

symbol × : N → N → N;
notation × infix left 7;
rule       0 × _  ↪ 0
with succ $x × $y ↪ $y + $x × $y;

assert x y z ⊢ x + y × z ≡ x + (y × z);

symbol ≤ : N → N → Prop;
notation ≤ infix left 3;

assert x y z ⊢ x + y ≤ z ≡ (x + y) ≤ z;

/////////////////// Arithmetic and boolean expressions

inductive Expr : TYPE ≔
 | Lit : N → Expr
 | Add : Expr → Expr → Expr
 | If  : BExpr → Expr → Expr → Expr
with BExpr : TYPE ≔
 | BLit : B → BExpr
 | And  : BExpr → BExpr → BExpr
 | Not  : BExpr → BExpr
 | Equal  : Expr → Expr → BExpr;

assert ⊢ Expr : TYPE;
assert ⊢ Lit : N → Expr;
assert ⊢ Add : Expr → Expr → Expr;
assert ⊢ If  : BExpr → Expr → Expr → Expr;
assert ⊢ BExpr : TYPE;
assert ⊢ BLit : B → BExpr;
assert ⊢ And  : BExpr → BExpr → BExpr;
assert ⊢ Not  : BExpr → BExpr;
assert ⊢ Equal  : Expr → Expr → BExpr;

assert ⊢ ind_Expr :
  Π p0: Expr → Prop, Π p1: BExpr → Prop,
    (Π x: N, π(p0 (Lit x))) →
    (Π x: Expr, π(p0 x) → Π x0: Expr, π(p0 x0) → π(p0 (Add x x0))) →
    (Π x: BExpr, π(p1 x) → Π x0: Expr, π(p0 x0) → Π x1: Expr, π(p0 x1) → π(p0 (If x x0 x1))) → 
    (Π x: B, π(p1 (BLit x))) →
    (Π x: BExpr, π(p1 x) → Π x0: BExpr, π(p1 x0) → π(p1 (And x x0))) →
    (Π x: BExpr, π(p1 x) → π(p1 (Not x))) →
    (Π x: Expr, π(p0 x) → Π x0: Expr, π(p0 x0) → π(p1 (Equal x x0))) →
  Π x: Expr, π(p0 x);

assert ⊢ ind_BExpr :
  Π p0: Expr → Prop, Π p1: BExpr → Prop,
    (Π x: N, π(p0 (Lit x))) →
    (Π x: Expr, π(p0 x) → Π x0: Expr, π(p0 x0) → π(p0 (Add x x0))) →
    (Π x: BExpr, π(p1 x) → Π x0: Expr, π(p0 x0) → Π x1: Expr, π(p0 x1) → π(p0 (If x x0 x1))) →
    (Π x: B, π(p1 (BLit x))) →
    (Π x: BExpr, π(p1 x) → Π x0: BExpr, π(p1 x0) → π(p1 (And x x0))) →
    (Π x: BExpr, π(p1 x) → π(p1 (Not x))) →
    (Π x: Expr, π(p0 x) → Π x0: Expr, π(p0 x0) → π(p1 (Equal x x0))) →
  Π x: BExpr, π(p1 x);

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual n
⊢ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual (Lit n) ≡ pLit n;

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1 e2
⊢ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
(Add e1 e2) ≡ pAdd
e1 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1)
e2 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e2);

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be1 e1 e2
⊢ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
(If be1 e1 e2) ≡ pIf
be1 (ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be1)
e1 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1)
e2 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e2);

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual x
⊢ ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual (BLit x) ≡ pBLit x;

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be1 be2
⊢ ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
(And be1 be2) ≡ pAnd
be1 (ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be1)
be2 (ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be2);

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be1
⊢ ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
(Not be1) ≡ pNot
be1 (ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual be1);

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1 e2
⊢ ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual
(Equal e1 e2) ≡ pEqual
e1 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1)
e2 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e2);

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual n
⊢ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual (Lit n) ≡ pLit n;

assert p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1 e2
⊢ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual (Add e1 e2)
≡ pAdd e1 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e1)
       e2 (ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual e2);

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
 | cAss  : Set → AExp → CExp // FIXME: What Set is doing here ?
 | cSeq  : CExp → CExp → CExp
 | cIf   : BExp → CExp → CExp → CExp;

assert ⊢ AExp : TYPE;
assert ⊢ aLit : N → AExp;
assert ⊢ aAdd : AExp → AExp → AExp;
assert ⊢ aIf  : BExp → AExp → AExp → AExp;
assert ⊢ BExp : TYPE;
assert ⊢ bLit : B → BExp;
assert ⊢ bEq : AExp → AExp → BExp;
assert ⊢ CExp : TYPE;
assert ⊢ cSkip : CExp;
assert ⊢ cAss  : Set → AExp → CExp;
assert ⊢ cSeq  : CExp → CExp → CExp;
assert ⊢ cIf   : BExp → CExp → CExp → CExp;

assert ⊢ ind_AExp :
  Π pA: AExp → Prop, Π pB: BExp → Prop, Π pC: CExp → Prop,
   (Π x: N, π(pA (aLit x))) →
   (Π x: AExp, π(pA x) → Π x0: AExp, π(pA x0) → π(pA (aAdd x x0))) →
   (Π x: BExp, π(pB x) → Π x0: AExp, π(pA x0) → Π x1: AExp, π(pA x1) → π(pA (aIf x x0 x1))) →
   (Π x: B, π(pB (bLit x))) →
   (Π x: AExp, π(pA x) → Π x0: AExp, π(pA x0) → π(pB (bEq x x0))) →
   π(pC cSkip) →
   (Π x: Set, Π x0: AExp, π(pA x0) → π(pC (cAss x x0))) →
   (Π x: CExp, π(pC x) → Π x0: CExp, π(pC x0) → π(pC (cSeq x x0))) →
   (Π x: BExp, π(pB x) → Π x0: CExp, π(pC x0) → Π x1: CExp, π(pC x1) → π(pC (cIf x x0 x1))) →
  Π x: AExp, π(pA x);

assert ⊢ ind_BExp :
  Π pA: AExp → Prop, Π pB: BExp → Prop, Π pC: CExp → Prop,
   (Π x: N, π(pA (aLit x))) →
   (Π x: AExp, π(pA x) → Π x0: AExp, π(pA x0) → π(pA (aAdd x x0))) →
   (Π x: BExp, π(pB x) → Π x0: AExp, π(pA x0) → Π x1: AExp, π(pA x1) → π(pA (aIf x x0 x1))) →
   (Π x: B, π(pB (bLit x))) →
   (Π x: AExp, π(pA x) → Π x0: AExp, π(pA x0) → π(pB (bEq x x0))) →
   π(pC cSkip) →
   (Π x: Set, Π x0: AExp, π(pA x0) → π(pC (cAss x x0))) →
   (Π x: CExp, π(pC x) → Π x0: CExp, π(pC x0) → π(pC (cSeq x x0))) →
   (Π x: BExp, π(pB x) → Π x0: CExp, π(pC x0) → Π x1: CExp, π(pC x1) → π(pC (cIf x x0 x1))) →
  Π x: BExp, π(pB x);

assert ⊢ ind_CExp :
  Π pA: AExp → Prop, Π pB: BExp → Prop, Π pC: CExp → Prop,
   (Π x: N, π(pA (aLit x))) →
   (Π x: AExp, π(pA x) → Π x0: AExp, π(pA x0) → π(pA (aAdd x x0))) →
   (Π x: BExp, π(pB x) → Π x0: AExp, π(pA x0) → Π x1: AExp, π(pA x1) → π(pA (aIf x x0 x1))) →
   (Π x: B, π(pB (bLit x))) →
   (Π x: AExp, π(pA x) → Π x0: AExp, π(pA x0) → π(pB (bEq x x0))) →
   π(pC cSkip) →
   (Π x: Set, Π x0: AExp, π(pA x0) → π(pC (cAss x x0))) →
   (Π x: CExp, π(pC x) → Π x0: CExp, π(pC x0) → π(pC (cSeq x x0))) →
   (Π x: BExp, π(pB x) → Π x0: CExp, π(pC x0) → Π x1: CExp, π(pC x1) → π(pC (cIf x x0 x1))) →
  Π x: CExp, π(pC x);

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf n
⊢ ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(aLit n) ≡ paLit n;

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a1 a2
⊢ ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(aAdd a1 a2) ≡ paAdd
a1 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a1)
a2 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a2);

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf b a1 a2
⊢ ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(aIf b a1 a2) ≡ paIf
b (ind_BExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf b)
a1 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a1)
a2 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a2);

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf x
⊢ ind_BExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(bLit x) ≡ pbLit x;

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a1 a2
⊢ ind_BExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(bEq a1 a2) ≡ pbEq
a1 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a1)
a2 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a2);

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
⊢ ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
cSkip ≡ pcSkip;

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf s a1
⊢ ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(cAss s a1) ≡ pcAss s
a1 (ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf a1);

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf c1 c2
⊢ ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(cSeq c1 c2) ≡ pcSeq
c1 (ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf c1)
c2 (ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf c2);

assert pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf b c1 c2
⊢ ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf
(cIf b c1 c2) ≡ pcIf
b (ind_BExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf b)
c1 (ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf c1)
c2 (ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf c2);

////////////////////// Even and odd

inductive even : N → TYPE ≔
  | even_O : even 0
  | even_S : Π n, odd n → even (succ n)
with odd : N → TYPE ≔
  | odd_S : Π n, even n → odd (succ n);

assert ⊢ even : N → TYPE;
assert ⊢ even_O : even 0;
assert ⊢ even_S : Π n, odd n → even (succ n);
assert ⊢ odd : N → TYPE;
assert ⊢ odd_S : Π n, even n → odd (succ n);

assert ⊢ ind_even :
  Π p0: Π x: N, even x → Prop, Π p1: Π x: N, odd x → Prop,
    π(p0 0 even_O) →
   (Π n: τ nat, Π x: odd n, π(p1 n x) → π(p0 (succ n) (even_S n x))) →
   (Π n: τ nat, Π x: even n, π(p0 n x) → π(p1 (succ n) (odd_S n x))) →
  Π x: N, Π x0: even x, π(p0 x x0);

assert ⊢ ind_odd :
  Π p0: Π x: N, even x → Prop, Π p1: Π x: N, odd x → Prop,
    π(p0 0 even_O) →
    (Π n: τ nat, Π x: odd n, π(p1 n x) → π(p0 (succ n) (even_S n x))) →
    (Π n: τ nat, Π x: even n, π(p0 n x) → π(p1 (succ n) (odd_S n x))) →
  Π x: N, Π x0: odd x, π(p1 x x0);

assert peven podd peven_O peven_S podd_S n evenn
⊢ ind_odd peven podd peven_O peven_S podd_S _ (odd_S n evenn)
≡ podd_S n evenn (ind_even peven podd peven_O peven_S podd_S _ evenn);

assert peven podd peven_O peven_S podd_S n evenn
⊢ ind_even peven podd peven_O peven_S podd_S _ even_O ≡ peven_O;

assert peven podd peven_O peven_S podd_S n oddn
⊢ ind_even peven podd peven_O peven_S podd_S _ (even_S n oddn)
≡ peven_S n oddn (ind_odd peven podd peven_O peven_S podd_S _ oddn);

////////////////////// Lists of natural numbers

inductive List : TYPE ≔
 | nil  : List
 | cons : N → List → List;

assert ⊢ List : TYPE;
assert ⊢ nil  : List;
assert ⊢ cons : N → List → List;

assert ⊢ ind_List :
  Π(p:List → Prop), π(p nil) → (Π x l,π(p l) → π(p(cons x l))) → Π l,π(p l);

assert p pnil pcons ⊢ ind_List p pnil pcons nil ≡ pnil;
assert p pnil pcons n l
⊢ ind_List p pnil pcons (cons n l) ≡ pcons n l (ind_List p pnil pcons l);

constant symbol list : Set;
rule τ list ↪ List;

///////////////// Pairs of natural numbers

inductive nat_prod : TYPE ≔ prod : N → N → nat_prod;

assert ⊢ nat_prod : TYPE;
assert ⊢ prod : N → N → nat_prod;

assert ⊢ ind_nat_prod :
Π p : nat_prod → Prop,
(Π x0 x1, π(p (prod x0 x1))) →
Π x, π(p x);

assert p pprod n1 n2 ⊢ ind_nat_prod p pprod (prod n1 n2) ≡ pprod n1 n2;

///////////////// Binary trees

inductive Tree : TYPE ≔
  | leaf : Tree
  | consTree : Tree → N → Tree → Tree;

assert ⊢ Tree : TYPE;
assert ⊢ leaf : Tree;
assert ⊢ consTree : Tree → N → Tree → Tree;

assert ⊢ ind_Tree : Π p,
π(p leaf) →
(Π t1, π(p t1) → Π x t2, π(p t2) → π(p (consTree t1 x t2))) →
Π t, π(p t);

assert p pleaf pconsTree ⊢ ind_Tree p pleaf pconsTree leaf ≡ pleaf;

assert p pleaf pconsTree t1 n t2
⊢ ind_Tree p pleaf pconsTree (consTree t1 n t2)
≡ pconsTree t1 (ind_Tree p pleaf pconsTree t1)
  n t2 (ind_Tree p pleaf pconsTree t2);

///////////////////// Polymorphic lists

(a:Set)
inductive L : TYPE ≔
| nilL  : L a
| consL : τ a → L a → L a;

assert ⊢ L : Set → TYPE;
assert ⊢ @nilL : Π a, L a;
assert ⊢ @consL : Π a, τ a → L a → L a;
assert ⊢ ind_L : Π a (p:L a → Prop),
  π(p nilL) → (Π x l, π(p l) → π(p (consL x l))) → Π l, π(p l);

assert a p pnil pcons ⊢ ind_L a p pnil pcons nilL ≡ pnil;
assert a p pnil pcons x l ⊢ ind_L a p pnil pcons (consL x l)
≡ pcons x l (ind_L a p pnil pcons l);

////////////////// Polymorphic trees

(a:Set)
inductive T:TYPE ≔
| node:τ a → F a → T a
with F:TYPE ≔
| nilF:F a
| consF:T a → F a → F a;

assert ⊢ T:Set → TYPE;
assert ⊢ F:Set → TYPE;
assert ⊢ @node:Π a, τ a → F a → T a;
assert ⊢ @nilF:Π a, F a;
assert ⊢ @consF:Π a, T a → F a → F a;

assert ⊢ ind_F: Π a, Π p:T a → Prop, Π q:F a → Prop,
  (Π x, Π l, π(q l) → π(p (node x l))) →
  π(q nilF) →
  (Π t, π(p t) → Π l, π(q l) → π(q (consF t l))) →
  Π l, π(q l);
assert ⊢ ind_T: Π a, Π p:T a → Prop, Π q:F a → Prop,
  (Π x, Π l, π(q l) → π(p (node x l))) →
  π(q nilF) →
  (Π t, π(p t) → Π l, π(q l) → π(q (consF t l))) →
  Π t, π(p t);

assert a p q pnode pnil pcons x l ⊢
  ind_T a p q pnode pnil pcons (node x l)
  ≡ pnode x l (ind_F a p q pnode pnil pcons l);
assert a p q pnode pnil pcons ⊢
  ind_F a p q pnode pnil pcons nilF
  ≡ pnil;
assert a p q pnode pnil pcons t l ⊢
  ind_F a p q pnode pnil pcons (consF t l)
  ≡ pcons t (ind_T a p q pnode pnil pcons t) l (ind_F a p q pnode pnil pcons l);

////////////////// Type sum - test names between {|...|} too

inductive {|sum|} : Set → Set → TYPE ≔
 | {|inl_sum|} : Π a b, τ a → {|sum|} a b
 | inr : Π a b, τ b → {|sum|} a b;

assert ⊢ {|sum|} : Set → Set → TYPE;
assert ⊢ {|inl_sum|} : Π a b, τ a → {|sum|} a b;
assert ⊢ inr : Π a b, τ b → {|sum|} a b;

assert ⊢ {|ind_sum|} : Π p,
(Π a b xa, π(p a b ({|inl_sum|} a b xa))) →
(Π a b xb, π(p a b (inr a b xb))) →
Π a b s, π(p a b s);

assert pS pinl pinr g d xg
⊢ {|ind_sum|} pS pinl pinr g d ({|inl_sum|} g d xg) ≡ pinl g d xg;
assert pS pinl pinr g d xd
⊢ {|ind_sum|} pS pinl pinr g d (inr g d xd) ≡ pinr g d xd;

//////////////////// Vectors of natural numbers

inductive V (n:N) : TYPE ≔
 | nil_vec : V z
 | cons_vec n : N → V n → V (succ n);

assert ⊢ V : N → TYPE;
assert ⊢ nil_vec   : V z;
assert ⊢ cons_vec  : Π n, N → V n → V (succ n);

assert ⊢ ind_V :
 Π p, π(p z nil_vec) → (Π n x v, π(p n v) → π(p (succ n) (cons_vec n x v))) → Π n v, π(p n v);

assert p pnil pcons ⊢ ind_V p pnil pcons z nil_vec ≡ pnil;
assert p pnil pcons n y v
⊢ ind_V p pnil pcons (succ n) (cons_vec n y v)
≡ pcons n y v (ind_V p pnil pcons n v);

/////////////////

inductive fin : N → TYPE ≔
  | new : Π n, fin (succ n)
  | inj : Π n, fin n → fin (succ n);

assert ⊢ fin : N → TYPE;
assert ⊢ new : Π n, fin (succ n);
assert ⊢ inj : Π n, fin n → fin (succ n);

assert ⊢ ind_fin :
  Π p, (Π n, π(p (succ n) (new n))) →
  (Π n f, π(p n f) → π(p (succ n) (inj n f))) →
  Π n f, π(p n f);

assert p pnew pinj n ⊢ ind_fin p pnew pinj (succ n) (new n) ≡ pnew n;

assert p pnew pinj n f
⊢ ind_fin p pnew pinj (succ n) (inj n f)
≡ pinj n f (ind_fin p pnew pinj n f);

///////////////// Bounded List

inductive blist : τ nat → TYPE ≔
 | bnil  : Π b, blist b
 | bcons : Π b x, π(x ≤ b) → blist b → blist b;

assert ⊢ blist : τ nat → TYPE;
assert ⊢ bnil  : Π b, blist b;
assert ⊢ bcons : Π b x, π(x ≤ b) → blist b → blist b;

assert ⊢ ind_blist :
Π p, (Π b, π(p b (bnil b))) →
(Π b x (prf:π(x ≤ b)) l, π(p b l) → π(p b (bcons b x prf l))) → 
Π b l, π(p b l);

assert p pnil pcons n ⊢ ind_blist p pnil pcons n (bnil n) ≡ pnil n;

assert p pnil pcons b x xb l
⊢ ind_blist p pnil pcons b (bcons b x xb l)
≡ pcons b x xb l (ind_blist p pnil pcons b l);

///////////////// Type rom

inductive rom : N → TYPE ≔
 | mty : rom z // leaf node
 | bin : Π e1 e2, rom e1 → rom e2 → rom (e1 + e2 + 1)  // binary nodes
 | unl : Π e k, π(k ≤ 2 × e) → rom e → rom (succ e); // unary labeled nodes

assert ⊢ rom : N → TYPE;
assert ⊢ mty : rom z;
assert ⊢ bin : Π e1 e2, rom e1 → rom e2 → rom (e1 + e2 + 1);
assert ⊢ unl : Π e k, π(k ≤ 2 × e) → rom e → rom (succ e);

assert ⊢ ind_rom : Π p: Π x: N, rom x → Prop,
  π(p 0 mty) →
  (Π e1:N, Π e2:N, Π x:rom e1, π(p e1 x) → Π x0:rom e2, π(p e2 x0) →
     π(p ((e1 + e2) + 1) (bin e1 e2 x x0))) → 
  (Π e:N, Π k:N, Π x:π(k ≤ (2 × e)), Π x0:rom e, π(p e x0) →
    π(p (succ e) (unl e k x x0))) → 
  Π x:N, Π x0:rom x, π(p x x0);

assert p pmty pbin punl ⊢ ind_rom p pmty pbin punl _ mty ≡ pmty;

assert p pmty pbin punl y n prf_le romy
⊢ ind_rom p pmty pbin punl _ (unl y n prf_le romy)
≡ punl y n prf_le romy (ind_rom p pmty pbin punl _ romy);

assert p pmty pbin punl y n romy romn
⊢ ind_rom p pmty pbin punl _ (bin y n romy romn)
≡ pbin y n romy (ind_rom p pmty pbin punl y romy)
  romn (ind_rom p pmty pbin punl n romn);

///////////////// Fibonacci suite

inductive fibo : N → N → TYPE ≔
 | cgen' : Π (n r1 r2 : N),
    fibo n r1 → fibo (succ n) r2 →  fibo (succ (succ n)) (r1 + r2)
 | cbase1 : fibo z (succ z)
 | cbase2 : fibo (succ z) (succ z);

assert ⊢ fibo : N → N → TYPE;
assert ⊢ cgen' : Π (n r1 r2 : N),
    fibo n r1 → fibo (succ n) r2 →  fibo (succ (succ n)) (r1 + r2);
assert ⊢ cbase1 : fibo z (succ z);
assert ⊢ cbase2 : fibo (succ z) (succ z);

assert ⊢ ind_fibo : Π p: Π x: N, Π x0: N, fibo x x0 → Prop,
  (Π n r1 r2,
     Π x0: fibo n r1, π(p n r1 x0) →
     Π x1: fibo (succ n) r2, π(p (succ n) r2 x1) →
  π(p (succ (succ n)) (r1 + r2) (cgen' n r1 r2 x0 x1))) →
  π(p 0 1 cbase1) →
  π(p 1 1 cbase2) →
  Π x:N, Π x0:N, Π x1:fibo x x0, π(p x x0 x1);

assert p pcgen' pcbase1 pcbase2 n r1 r2 hypF1 hypF2
⊢ ind_fibo p pcgen' pcbase1 pcbase2 _ _ (cgen' n r1 r2 hypF1 hypF2)
≡ pcgen' n r1 r2 hypF1 (ind_fibo p pcgen' pcbase1 pcbase2 _ _ hypF1) 
                 hypF2 (ind_fibo p pcgen' pcbase1 pcbase2 _ _ hypF2);

assert p pcgen' pcbase1 pcbase2
⊢ ind_fibo p pcgen' pcbase1 pcbase2 _ _ cbase1 ≡ pcbase1;

assert p pcgen' pcbase1 pcbase2
⊢ ind_fibo p pcgen' pcbase1 pcbase2 _ _ cbase2 ≡ pcbase2;

/////////////////// Polymorphic vector

inductive Vec : Set → N → TYPE ≔
 | Vnil   : Π a, Vec a z
 | Vcons  : Π a n (_:τ a), Vec a n → Vec a (succ n);

assert ⊢ Vec : Set → N → TYPE;
assert ⊢ Vnil   : Π a, Vec a z;
assert ⊢ Vcons  : Π a n (_:τ a), Vec a n → Vec a (succ n);

assert ⊢ ind_Vec :
  Π p, (Π a, π(p a z (Vnil a))) → (Π a n x v, π(p a n v) → π(p a (succ n) (Vcons a n x v))) → Π a n v, π(p a n v);

assert p pnil a ⊢ ind_Vec p pnil _ _ _ (Vnil a) ≡ pnil a;

assert p pnil pcons a n x v
⊢ ind_Vec p pnil pcons _ _ (Vcons a n x v)
≡ pcons a n x v (ind_Vec p pnil pcons a n v);

/////////////////////////////
// Equality
/////////////////////////////

constant symbol = {a} : τ a → τ a → Prop;
notation = infix 1;
constant symbol eq_refl {a} (x : τ a) : π(x = x);
constant symbol eq_ind {a} (x y : τ a) : π(x = y) → Π p, π(p y) → π(p x);

// Set builtins for the rewrite tactic
builtin "T"     ≔ τ;
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ eq_ind;

/////////////////////////////
// Some proofs
/////////////////////////////

unif_rule τ $x ≡ N ↪ [ $x ≡ nat ];
//FIXME: should be infered from injectivity of τ

opaque symbol plus_0_n n : π(0 + n = n) ≔
begin
  assume n;
  reflexivity;
end;

opaque symbol plus_n_0 (n:N) : π(n + 0 = n) ≔
begin
  induction;
  // Case n = O
  reflexivity;
  // Case n = S n'
  assume n' Hn';
  simpl;
  rewrite Hn';
  reflexivity;
end;

// About lists

symbol length : List → N;
rule length nil ↪ 0
 with length (cons _ $l) ↪ succ (length $l);

symbol app : List → List → List;
rule  app      nil     $m ↪ $m
 with app (cons $x $l) $m ↪ cons $x (app $l $m);

opaque symbol length_app (l2 l1 : List):
  π(length l1 + length l2 = length (app l1 l2)) ≔
begin
  assume l2;
  induction;
  reflexivity;
  assume x l2 IHl1;
  simpl;
  rewrite IHl1;
  reflexivity;
end;
