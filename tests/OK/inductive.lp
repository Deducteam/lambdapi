/////////////////////////////
// Some examples of inductive types
/////////////////////////////

// Configuration

constant symbol Prop : TYPE;      // Type of propositions
set builtin "Prop" ≔ Prop;

injective symbol π : Prop → TYPE; // Interpretation of propositions in TYPE
set builtin "P" ≔ π;

constant symbol Set : TYPE;       // Type of set codes
injective symbol τ : Set → TYPE;  // Interpretation of set codes in TYPE

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
  π (p red) → π (p green) → π (p blue) →
  Π x, π (p x);

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
  π (p black) → π (p white) → (Π x, π (p (primary x))) →
  Π x, π (p x);

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
  π (p true) → π (p false) →
  Π b, π (p b);

assert p ptrue pfalse ⊢ ind_B p ptrue pfalse true ≡ ptrue;
assert p ptrue pfalse ⊢ ind_B p ptrue pfalse false ≡ pfalse;

constant symbol bool : Set;
rule B ↪ τ bool;

////////////////// False (empty type)

inductive False : TYPE ≔ /* no constructor */ ;

assert ⊢ False : TYPE;
assert ⊢ ind_False : Π(p:False → Prop) (f : False), π (p f);

///////////////// Natural numbers

inductive N : TYPE ≔
 | z    : N
 | succ : N → N;

assert ⊢ N : TYPE;
assert ⊢ z : N;
assert ⊢ succ : N → N;

assert ⊢ ind_N :
  Π p:N → Prop, π(p z) → (Π x, π (p x) → π (p (succ x))) → Π x, π (p x);

assert p pz psucc ⊢ ind_N p pz psucc z ≡ pz;
assert p pz psucc n ⊢ ind_N p pz psucc (succ n) ≡ psucc n (ind_N p pz psucc n);

constant symbol nat : Set;
rule N ↪ τ nat;

set builtin "0"  ≔ z;
set builtin "+1" ≔ succ;

symbol plus : N → N → N;
set infix left 6 "+" ≔ plus;
rule       0 + $y ↪ $y
with succ $x + $y ↪ succ ($x + $y);

symbol mult : N → N → N;
set infix left 7 "×" ≔ mult;
rule       0 × _  ↪ 0
with succ $x × $y ↪ $y + $x × $y;

assert x y z ⊢ x + y × z ≡ x + (y × z);

symbol le : N → N → Prop;
set infix left 3 "≤" ≔ le;

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
    (Π x: N, π (p0 (Lit x))) →
    (Π x: Expr, π (p0 x) → Π x0: Expr, π (p0 x0) → π (p0 (Add x x0))) →
    (Π x: BExpr, π (p1 x) → Π x0: Expr, π (p0 x0) → Π x1: Expr, π (p0 x1) → π (p0 (If x x0 x1))) → 
    (Π x: B, π (p1 (BLit x))) →
    (Π x: BExpr, π (p1 x) → Π x0: BExpr, π (p1 x0) → π (p1 (And x x0))) →
    (Π x: BExpr, π (p1 x) → π (p1 (Not x))) →
    (Π x: Expr, π (p0 x) → Π x0: Expr, π (p0 x0) → π (p1 (Equal x x0))) →
  Π x: Expr, π (p0 x);

assert ⊢ ind_BExpr :
  Π p0: Expr → Prop, Π p1: BExpr → Prop,
    (Π x: N, π (p0 (Lit x))) →
    (Π x: Expr, π (p0 x) → Π x0: Expr, π (p0 x0) → π (p0 (Add x x0))) →
    (Π x: BExpr, π (p1 x) → Π x0: Expr, π (p0 x0) → Π x1: Expr, π (p0 x1) → π (p0 (If x x0 x1))) →
    (Π x: B, π (p1 (BLit x))) →
    (Π x: BExpr, π (p1 x) → Π x0: BExpr, π (p1 x0) → π (p1 (And x x0))) →
    (Π x: BExpr, π (p1 x) → π (p1 (Not x))) →
    (Π x: Expr, π (p0 x) → Π x0: Expr, π (p0 x0) → π (p1 (Equal x x0))) →
  Π x: BExpr, π (p1 x);

symbol p0 : Expr → Prop;
symbol p1 : BExpr → Prop;
symbol pLit : Π x: N, π (p0 (Lit x));
symbol pAdd : Π x: Expr, π (p0 x) → Π x0: Expr, π (p0 x0) → π (p0 (Add x x0));
symbol pIf : Π x: BExpr, π (p1 x) → Π x0: Expr, π (p0 x0) → Π x1: Expr, π (p0 x1) → π (p0 (If x x0 x1));
symbol pBLit : Π x: B, π (p1 (BLit x));
symbol pAnd : Π x: BExpr, π (p1 x) → Π x0: BExpr, π (p1 x0) → π (p1 (And x x0));
symbol pNot : Π x: BExpr, π (p1 x) → π (p1 (Not x));
symbol pEqual : Π x: Expr, π (p0 x) → Π x0: Expr, π (p0 x0) → π (p1 (Equal x x0));
symbol indE ≔ ind_Expr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual;
symbol indBE ≔ ind_BExpr p0 p1 pLit pAdd pIf pBLit pAnd pNot pEqual;
symbol x : B;
symbol e1 : Expr;
symbol e2 : Expr;
symbol be1 : BExpr;
symbol be2 : BExpr;
symbol n : N;
assert ⊢ indE (Lit n) ≡ pLit n;
assert ⊢ indE (Add e1 e2) ≡ pAdd e1 (indE e1) e2 (indE e2);
assert ⊢ indE (If be1 e1 e2) ≡ pIf be1 (indBE be1) e1 (indE e1) e2 (indE e2);
assert ⊢ indBE (BLit x) ≡ pBLit x;
assert ⊢ indBE (And be1 be2) ≡ pAnd be1 (indBE be1) be2 (indBE be2);
assert ⊢ indBE (Not be1) ≡ pNot be1 (indBE be1);
assert ⊢ indBE (Equal e1 e2) ≡ pEqual e1 (indE e1) e2 (indE e2);

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
   (Π x: N, π (pA (aLit x))) →
   (Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pA (aAdd x x0))) →
   (Π x: BExp, π (pB x) → Π x0: AExp, π (pA x0) → Π x1: AExp, π (pA x1) → π (pA (aIf x x0 x1))) →
   (Π x: B, π (pB (bLit x))) →
   (Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pB (bEq x x0))) →
   π (pC cSkip) →
   (Π x: Set, Π x0: AExp, π (pA x0) → π (pC (cAss x x0))) →
   (Π x: CExp, π (pC x) → Π x0: CExp, π (pC x0) → π (pC (cSeq x x0))) →
   (Π x: BExp, π (pB x) → Π x0: CExp, π (pC x0) → Π x1: CExp, π (pC x1) → π (pC (cIf x x0 x1))) →
  Π x: AExp, π (pA x);

assert ⊢ ind_BExp :
  Π pA: AExp → Prop, Π pB: BExp → Prop, Π pC: CExp → Prop,
   (Π x: N, π (pA (aLit x))) →
   (Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pA (aAdd x x0))) →
   (Π x: BExp, π (pB x) → Π x0: AExp, π (pA x0) → Π x1: AExp, π (pA x1) → π (pA (aIf x x0 x1))) →
   (Π x: B, π (pB (bLit x))) →
   (Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pB (bEq x x0))) →
   π (pC cSkip) →
   (Π x: Set, Π x0: AExp, π (pA x0) → π (pC (cAss x x0))) →
   (Π x: CExp, π (pC x) → Π x0: CExp, π (pC x0) → π (pC (cSeq x x0))) →
   (Π x: BExp, π (pB x) → Π x0: CExp, π (pC x0) → Π x1: CExp, π (pC x1) → π (pC (cIf x x0 x1))) →
  Π x: BExp, π (pB x);

assert ⊢ ind_CExp :
  Π pA: AExp → Prop, Π pB: BExp → Prop, Π pC: CExp → Prop,
   (Π x: N, π (pA (aLit x))) →
   (Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pA (aAdd x x0))) →
   (Π x: BExp, π (pB x) → Π x0: AExp, π (pA x0) → Π x1: AExp, π (pA x1) → π (pA (aIf x x0 x1))) →
   (Π x: B, π (pB (bLit x))) →
   (Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pB (bEq x x0))) →
   π (pC cSkip) →
   (Π x: Set, Π x0: AExp, π (pA x0) → π (pC (cAss x x0))) →
   (Π x: CExp, π (pC x) → Π x0: CExp, π (pC x0) → π (pC (cSeq x x0))) →
   (Π x: BExp, π (pB x) → Π x0: CExp, π (pC x0) → Π x1: CExp, π (pC x1) → π (pC (cIf x x0 x1))) →
  Π x: CExp, π (pC x);

symbol pA : AExp → Prop;
symbol pB : BExp → Prop;
symbol pC : CExp → Prop;
symbol paLit : Π x: N, π (pA (aLit x));
symbol paAdd : Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pA (aAdd x x0));
symbol paIf : Π x: BExp, π (pB x) → Π x0: AExp, π (pA x0) → Π x1: AExp, π (pA x1) → π (pA (aIf x x0 x1));
symbol pbLit : Π x: B, π (pB (bLit x));
symbol pbEq :Π x: AExp, π (pA x) → Π x0: AExp, π (pA x0) → π (pB (bEq x x0));
symbol pcSkip : π (pC cSkip);
symbol pcAss : Π x: Set, Π x0: AExp, π (pA x0) → π (pC (cAss x x0));
symbol pcSeq : Π x: CExp, π (pC x) → Π x0: CExp, π (pC x0) → π (pC (cSeq x x0));
symbol pcIf : Π x: BExp, π (pB x) → Π x0: CExp, π (pC x0) → Π x1: CExp, π (pC x1) → π (pC (cIf x x0 x1));
symbol indA ≔ ind_AExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf;
symbol indB ≔ ind_BExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf;
symbol indC ≔ ind_CExp pA pB pC paLit paAdd paIf pbLit pbEq pcSkip pcAss pcSeq pcIf;
symbol a1 : AExp;
symbol a2 : AExp;
symbol b : BExp;
symbol c1 : CExp;
symbol c2 : CExp;
symbol s : Set;
assert ⊢ indA (aLit n) ≡ paLit n;
assert ⊢ indA (aAdd a1 a2) ≡ paAdd a1 (indA a1) a2 (indA a2);
assert ⊢ indA (aIf b a1 a2) ≡ paIf b (indB b) a1 (indA a1) a2 (indA a2);
assert ⊢ indB (bLit x) ≡ pbLit x;
assert ⊢ indB (bEq a1 a2) ≡ pbEq a1 (indA a1) a2 (indA a2);
assert ⊢ indC cSkip ≡ pcSkip;
assert ⊢ indC (cAss s a1) ≡ pcAss s a1 (indA a1);
assert ⊢ indC (cSeq c1 c2) ≡ pcSeq c1 (indC c1) c2 (indC c2);
assert ⊢ indC (cIf b c1 c2) ≡ pcIf b (indB b) c1 (indC c1) c2 (indC c2);

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
    π (p0 0 even_O) →
   (Π n: τ nat, Π x: odd n, π (p1 n x) → π (p0 (succ n) (even_S n x))) →
   (Π n: τ nat, Π x: even n, π (p0 n x) → π (p1 (succ n) (odd_S n x))) →
  Π x: N, Π x0: even x, π (p0 x x0);

assert ⊢ ind_odd :
  Π p0: Π x: N, even x → Prop, Π p1: Π x: N, odd x → Prop,
    π (p0 0 even_O) →
    (Π n: τ nat, Π x: odd n, π (p1 n x) → π (p0 (succ n) (even_S n x))) →
    (Π n: τ nat, Π x: even n, π (p0 n x) → π (p1 (succ n) (odd_S n x))) →
  Π x: N, Π x0: odd x, π (p1 x x0);

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
rule List ↪ τ list;

///////////////// Pairs of natural numbers

inductive nat_prod : TYPE ≔ prod : N → N → nat_prod;

assert ⊢ nat_prod : TYPE;
assert ⊢ prod : N → N → nat_prod;

assert ⊢ ind_nat_prod :
Π p : nat_prod → Prop,
(Π x0 x1, π (p (prod x0 x1))) →
Π x, π (p x);

assert p pprod n1 n2 ⊢ ind_nat_prod p pprod (prod n1 n2) ≡ pprod n1 n2;

///////////////// Binary trees

inductive Tree : TYPE ≔
  | leaf : Tree
  | consTree : Tree → N → Tree → Tree;

assert ⊢ Tree : TYPE;
assert ⊢ leaf : Tree;
assert ⊢ consTree : Tree → N → Tree → Tree;

assert ⊢ ind_Tree : Π p,
π (p leaf) →
(Π t1, π (p t1) → Π x t2, π (p t2) → π (p (consTree t1 x t2))) →
Π t, π (p t);

assert p pleaf pconsTree ⊢ ind_Tree p pleaf pconsTree leaf ≡ pleaf;
assert p pleaf pconsTree t1 x t2
⊢ ind_Tree p pleaf pconsTree (consTree t1 n t2)
≡ pconsTree t1 (ind_Tree p pleaf pconsTree t1)
  n t2 (ind_Tree p pleaf pconsTree t2);

///////////////////// Polymorphic list

(a:Set)
inductive L : TYPE ≔
| nilL  : L a
| consL : τ a → L a → L a;

assert ⊢ L : Set → TYPE;
assert ⊢ @nilL : Π a, L a;
assert ⊢ @consL : Π a, τ a → L a → L a;
assert ⊢ ind_L : Π a p,
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
(Π a b xa, π (p a b ({|inl_sum|} a b xa))) →
(Π a b xb, π (p a b (inr a b xb))) →
Π a b s, π (p a b s);

assert pS pinl pinr g d xg
⊢ {|ind_sum|} pS pinl pinr g d ({|inl_sum|} g d xg) ≡ pinl g d xg;
assert pS pinl pinr g d xd
⊢ {|ind_sum|} pS pinl pinr g d (inr g d xd) ≡ pinr g d xd;

//////////////////// Vectors of natural numbers

inductive V : N → TYPE ≔
 | nil_vec   : V z
 | cons_vec  : Π n, N → V n → V (succ n);

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
  Π p, (Π n, π (p (succ n) (new n))) → (Π n f, π (p n f) → π (p (succ n) (inj n f))) → Π n f, π (p n f);

symbol pF : Π n, fin n → Prop;
symbol pnew : Π n, π (pF (succ n) (new n));
symbol pinj : Π n f, π (pF n f) → π (pF (succ n) (inj n f));
symbol indF ≔ ind_fin pF pnew pinj;
symbol f : fin n;
assert ⊢ indF (succ n) (new n) ≡ pnew n;
assert ⊢ indF (succ n) (inj n f) ≡ pinj n f (indF n f);

///////////////// Bounded List

inductive blist : τ nat → TYPE ≔
 | bnil  : Π b, blist b
 | bcons : Π b x, π (x ≤ b) → blist b → blist b;

assert ⊢ blist : τ nat → TYPE;
assert ⊢ bnil  : Π b, blist b;
assert ⊢ bcons : Π b x, π (x ≤ b) → blist b → blist b;

assert ⊢ ind_blist :
Π p, (Π b, π(p b (bnil b))) →
(Π b x (prf:π (x ≤ b)) l, π(p b l) → π(p b (bcons b x prf l))) → 
Π b l, π(p b l);

assert p pnil pcons n ⊢ ind_blist p pnil pcons n (bnil n) ≡ pnil n;

assert p pnil pcons b x xb l
⊢ ind_blist p pnil pcons b (bcons b x xb l)
≡ pcons b x xb l (ind_blist p pnil pcons b l);

///////////////// Type rom

inductive rom : N → TYPE ≔
 | mty : rom z // leaf node
 | bin : Π e1 e2, rom e1 → rom e2 → rom (e1 + e2 + 1)  // binary nodes
 | unl : Π e k, π (k ≤ 2 × e) → rom e → rom (succ e); // unary labeled nodes

assert ⊢ rom : N → TYPE;
assert ⊢ mty : rom z;
assert ⊢ bin : Π e1 e2, rom e1 → rom e2 → rom (e1 + e2 + 1);
assert ⊢ unl : Π e k, π (k ≤ 2 × e) → rom e → rom (succ e);

assert ⊢ ind_rom : Π p: Π x: N, rom x → Prop,
  π (p 0 mty) →
  (Π e1: τ nat, Π e2: τ nat, Π x: rom e1, π (p e1 x) → Π x0: rom e2, π (p e2 x0) → π (p ((e1 + e2) + 1) (bin e1 e2 x x0))) → 
  (Π e: τ nat, Π k: τ nat, Π x: π (k ≤ (2 × e)), Π x0: rom e, π (p e x0) → π (p (succ e) (unl e k x x0))) → 
Π x: N, Π x0: rom x, π (p x x0);

symbol pRom : Π x: N, rom x → Prop;
symbol pmty : π (pRom z mty);
symbol pbin : Π e1: τ nat, Π e2: τ nat, Π x: rom e1,
 π (pRom e1 x) → Π x0: rom e2, π (pRom e2 x0) → π (pRom ((e1 + e2) + 1) (bin e1 e2 x x0));
symbol punl : Π e: τ nat, Π k: τ nat, Π x: π (k ≤ (2 × e)), Π x0: rom e, π (pRom e x0) → π (pRom (succ e) (unl e k x x0));
symbol indr ≔ ind_rom pRom pmty pbin punl;
symbol y:N;
symbol prf_le : π (n ≤ 2 × y);
symbol romy : rom y;
symbol romn : rom n;
assert ⊢ indr _ mty ≡ pmty;
assert ⊢ indr _ (unl y n prf_le romy) ≡ punl y n prf_le romy (indr _ romy);
assert ⊢ indr _ (bin y n romy romn) ≡ pbin y n romy (indr y romy) romn (indr n romn);

///////////////// Fibonacci suite

inductive fibo : N → N → TYPE ≔
 | cgen' : Π (n r1 r2 : N),
    fibo n r1 → fibo (succ n) r2 →  fibo (succ (succ n)) (plus r1 r2)
 | cbase1 : fibo z (succ z)
 | cbase2 : fibo (succ z) (succ z);

assert ⊢ fibo : N → N → TYPE;
assert ⊢ cgen' : Π (n r1 r2 : N),
    fibo n r1 → fibo (succ n) r2 →  fibo (succ (succ n)) (plus r1 r2);
assert ⊢ cbase1 : fibo z (succ z);
assert ⊢ cbase2 : fibo (succ z) (succ z);

assert ⊢ ind_fibo : Π p: Π x: N, Π x0: N, fibo x x0 → Prop,
(Π n r1 r2,
     Π x0: fibo n r1, π (p n r1 x0) →
     Π x1: fibo (succ n) r2, π (p (succ n) r2 x1) →
π (p (succ (succ n)) (r1 + r2) (cgen' n r1 r2 x0 x1))) →
π (p 0 1 cbase1) →
π (p 1 1 cbase2) →
Π x: N, Π x0: N, Π x1: fibo x x0, π (p x x0 x1);

symbol pFibo : Π x: N, Π x0: N, fibo x x0 → Prop;
symbol pcgen' : (Π n r1 r2, Π x0: fibo n r1, π (pFibo n r1 x0) →
  Π x1: fibo (succ n) r2, π (pFibo (succ n) r2 x1) →
  π (pFibo (succ (succ n)) (r1 + r2) (cgen' n r1 r2 x0 x1)));
symbol pcbase1 : π (pFibo 0 1 cbase1);
symbol pcbase2 : π (pFibo 1 1 cbase2);
symbol indfibo ≔ ind_fibo pFibo pcgen' pcbase1 pcbase2;
symbol r1 : N;
symbol r2 : N;
symbol hypF1 : fibo n r1;
symbol hypF2 : fibo (succ n) r2;
assert ⊢ indfibo _ _ (cgen' n r1 r2 hypF1 hypF2)
     ≡ pcgen' n r1 r2 hypF1 (indfibo _ _ hypF1) 
                      hypF2 (indfibo _ _ hypF2);
assert ⊢ indfibo _ _ cbase1 ≡ pcbase1;
assert ⊢ indfibo _ _ cbase2 ≡ pcbase2;

/////////////////// Polymorphic vector

inductive Vec : Set → N → TYPE ≔
 | Vnil   : Π a, Vec a z
 | Vcons  : Π a n (_:τ a), Vec a n → Vec a (succ n);

assert ⊢ Vec : Set → N → TYPE;
assert ⊢ Vnil   : Π a, Vec a z;
assert ⊢ Vcons  : Π a n (_:τ a), Vec a n → Vec a (succ n);

assert ⊢ ind_Vec :
  Π p, (Π a, π(p a z (Vnil a))) → (Π a n x v, π(p a n v) → π(p a (succ n) (Vcons a n x v))) → Π a n v, π(p a n v);

symbol pVec : Π a n, Vec a n → Prop;
symbol pVecnil : Π a, π (pVec a z (Vnil a));
symbol pVeccons : Π a n x v, π(pVec a n v) → π(pVec a (succ n) (Vcons a n x v));
symbol indVec ≔ ind_Vec pVec pVecnil pVeccons;
symbol a : Set;
symbol xV_p : τ a;
symbol v_p : Vec a n;
assert ⊢ ind_Vec pVec pVecnil _ a z (Vnil a) ≡ pVecnil a;
assert ⊢ indVec a (succ n) (Vcons a n xV_p v_p)
     ≡ pVeccons a n xV_p v_p (indVec a n v_p);

////////////////// Type Bush (nested inductive type)

symbol bush : Set →  Set;

inductive Bush : Π(_:Set), TYPE ≔
 | bempty : Π a, Bush a
 | bush_cons : Π a, τ a → Bush (bush a) → Bush a;

rule Bush $a ↪ τ (bush $a);

assert ⊢ Bush : Π(_:Set), TYPE;
assert ⊢ bempty : Π a, Bush a;
assert ⊢ bush_cons : Π a, τ a → Bush (bush a) → Bush a;

assert ⊢ ind_Bush :
  Π p, (Π a, π(p a (bempty a))) → (Π a x l, π(p (bush a) l) → π(p a (bush_cons a x l))) → Π a l, π(p a l);

symbol pBush : Π a, Bush a → Prop;
symbol pbempty : Π a, π (pBush a (bempty a));
symbol pbush_cons : Π a x l, π (pBush (bush a) l) → π (pBush a (bush_cons a x l));
symbol indbush ≔ ind_Bush pBush pbempty pbush_cons;
symbol tb : Bush (bush a);
assert ⊢ indbush a (bempty a) ≡ pbempty a;
symbol xa : τ a;
assert ⊢ indbush a (bush_cons a xa tb) ≡ pbush_cons a xa tb (indbush (bush a) tb);

/////////////////////////////
// Equality
/////////////////////////////

constant symbol eq {a} : τ a → τ a → Prop;
set infix 1 "=" ≔ eq;
constant symbol eq_refl {a} (x : τ a) : π (x = x);
constant symbol eq_ind {a} (x y : τ a) : π (x = y) → Π p, π (p y) → π (p x);

// Set builtins for the rewrite tactic
set builtin "T"     ≔ τ;
set builtin "eq"    ≔ eq;
set builtin "refl"  ≔ eq_refl;
set builtin "eqind" ≔ eq_ind;

/////////////////////////////
// Some proofs
/////////////////////////////

opaque symbol plus_0_n : Π n, π (0 + n = n) ≔
begin
  assume n;
  reflexivity;
end;

opaque symbol plus_n_0 n : π (n + 0 = n) ≔
begin
  assume n;
  refine ind_N (λ z, z + 0 = z) _ _ _;
  // Case n = O
  refine eq_refl 0;
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

opaque symbol length_app :
  Π(l1 l2 : List), π ((length l1 + length l2) = length (app l1 l2)) ≔
begin
  assume l1 l2;
  apply ind_List
        (λ z, length z + length l2 = length (app z l2)) _ _ l1;
  reflexivity;
  assume x l2 IHl1;
  simpl; rewrite IHl1; reflexivity;
end;
