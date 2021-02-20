require open tests.OK.bool;
require open tests.OK.nat;

// Type of data type.

constant symbol U : TYPE;

// Interpretation function (for data types as types).

injective symbol T : U → TYPE;

// Examples of data types and their interpretations.

constant symbol bool : U;
constant symbol nat  : U;
constant symbol pi   : Π (a : U), (T a → U) → U;

rule T bool       ↪ B;
rule T nat        ↪ N;
rule T (pi $a $f) ↪ Π (x : T $a), T ($f x);

// Type of propositions and their interpretation as types.

constant symbol Prop : TYPE;

constant symbol all : Π (a : U), (T a → Prop) → Prop;

// Interpretation function (for propositions as types).

injective symbol P : Prop → TYPE;

rule P (all $a $f) ↪ Π (x : T $a), P ($f x);

// Induction principle on B.

symbol bool_ind : Π(p:B → Prop), P(p true) → P(p false) → Π b, P(p b);

rule bool_ind _ $t _  true  ↪ $t;
rule bool_ind _ _  $f false ↪ $f;

// Induction principle on N.

symbol nat_ind : Π (p:N → Prop), P(p z) → (Π n, P(p n) → P(p (s n))) → Π n, P(p n);

rule nat_ind _  $u _  z      ↪ $u;
rule nat_ind $p $u $v (s $n) ↪ $v $n (nat_ind $p $u $v $n);

// Leibniz equality.

constant symbol = {a} : T a → T a → Prop;
set notation = infix 1;

constant symbol refl  : Π a (x:T a), P (x = x);
constant symbol eqind : Π a x y, P (x = y) → Π p:T a → Prop, P (p y) → P (p x);

// Definition of connectors
constant symbol bot        : Prop;
constant symbol top        : Prop;
constant symbol imp        : Prop → Prop → Prop;
constant symbol {|and|}    : Prop → Prop → Prop;
constant symbol or         : Prop → Prop → Prop;
constant symbol not        : Prop → Prop;

// Axioms of Classical Natural Deduction

// Intro and Elimination of not
symbol not_elim         : Π (p : Prop), P (not p) → P p → P bot;
symbol not_intro        : Π (p : Prop), (P p → P bot) → P (not p);

// Bot elimation
symbol bot_elim         : Π (p : Prop), P bot → P p;

// Excluded middle
symbol excl_mid         : Π (p : Prop), P (or p (not p));

// Intro and Elimination of and
symbol and_intro        : Π (p : Prop) (q : Prop), P p → P q → P ({|and|} p q);
symbol and_elim1        : Π (p : Prop) (q : Prop), P ({|and|} p q) → P p;
symbol and_elim2        : Π (p : Prop) (q : Prop), P ({|and|} p q) → P q;

// Intro and Elimination of or
symbol or_intro1        : Π (p : Prop) (q : Prop), P p → P (or p q);
symbol or_intro2        : Π (p : Prop) (q : Prop), P q → P (or p q);
symbol or_elim          : Π (p : Prop) (q : Prop) (c : Prop), P (or p q) → (P p → P c) → (P q → P c) → P c;

// Intro and Elimination of imp
symbol imp_intro        : Π (p : Prop) (q : Prop), (P p → P q) → P (imp p q);
symbol imp_elim         : Π (p : Prop) (q : Prop), P (imp p q) → P p → P q;


opaque symbol not_elimp : Π (A : Prop), P (not (not A)) → P A
≔ begin
    assume A nnp;
    refine or_elim A (not A) A _ _ _;
    refine excl_mid A;
    assume pa;
    refine pa;
    assume pna;
    apply bot_elim;
    apply not_elim (not A) nnp;
    apply pna;
end;

set builtin "P"     ≔ P;
set builtin "T"     ≔ T;
set builtin "eq"    ≔ =;
set builtin "eqind" ≔ eqind;
set builtin "refl"  ≔ refl;

set builtin "bot"   ≔ bot;
set builtin "top"   ≔ top;
set builtin "imp"   ≔ imp;
set builtin "and"   ≔ {|and|};
set builtin "or"    ≔ or;
set builtin "not"   ≔ not;
