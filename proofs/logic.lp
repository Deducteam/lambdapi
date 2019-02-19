require open proofs.bool
require open proofs.nat

// Type of data type.

symbol const U : TYPE

// Interpretation function (for data types as types).

symbol injective T : U ⇒ TYPE

// Examples of data types and their interpretations.

symbol const bool : U
symbol const nat  : U
symbol const pi   : ∀ (a : U), (T a ⇒ U) ⇒ U

rule T bool       → B
rule T nat        → N
rule T (pi &a &f) → ∀ (x : T &a), T (&f x)

// Type of propositions and their interpretation as types.

symbol const Prop : TYPE

symbol const all : ∀ (a : U), (T a ⇒ Prop) ⇒ Prop

// Interpretation function (for propositions as types).

symbol injective P : Prop ⇒ TYPE

rule P (all &a &f) → ∀ (x : T &a), P (&f x)

// Induction principle on B.

symbol bool_ind : ∀ (p:B⇒Prop), P(p true) ⇒ P(p false) ⇒ ∀b, P(p b)

rule bool_ind _ &t _  true  → &t
rule bool_ind _ _  &f false → &f

// Induction principle on N.

symbol nat_ind : ∀ (p:N⇒Prop), P(p z) ⇒ (∀n, P(p n) ⇒ P(p (s n))) ⇒ ∀n, P(p n)

rule nat_ind _  &u _  z      → &u
rule nat_ind &p &u &v (s &n) → &v &n (nat_ind &p &u &v &n)

// Leibniz equality.

symbol const eq : ∀a, T a ⇒ T a ⇒ Prop

symbol const refl  : ∀a x, P (eq a x x)
symbol const eqind : ∀a x y, P (eq a x y) ⇒ ∀ (p:T a⇒Prop), P (p y) ⇒ P (p x)

// Definition of connectors 
symbol const bot        : Prop
symbol const imp        : Prop ⇒ Prop ⇒ Prop
symbol const {|and|}    : Prop ⇒ Prop ⇒ Prop
symbol const or         : Prop ⇒ Prop ⇒ Prop
symbol const not        : Prop ⇒ Prop

// Axioms of Classical Natural Deduction 

// Definition of not
rule P (not &a)         → P &a ⇒ P bot

// Bot elimation
symbol bot_elim         : ∀ (p : Prop), P bot ⇒ P p

// Excluded middle
symbol excl_mid         : ∀ (p : Prop), P (or p (not p))

// Intro and Elimination of and
symbol and_intro        : ∀ (p : Prop) (q : Prop), P p ⇒ P q ⇒ P ({|and|} p q)
symbol and_elim1        : ∀ (p : Prop) (q : Prop), P ({|and|} p q) ⇒ P p
symbol and_elim2        : ∀ (p : Prop) (q : Prop), P ({|and|} p q) ⇒ P q

// Intro and Elimination of or
symbol or_intro1        : ∀ (p : Prop) (q : Prop), P p ⇒ P (or p q)
symbol or_intro2        : ∀ (p : Prop) (q : Prop), P q ⇒ P (or p q)
symbol or_elim          : ∀ (p : Prop) (q : Prop) (c : Prop), P (or p q) ⇒ (P p ⇒ P c) ⇒ (P q ⇒ P c) ⇒ P c 

// Intro and Elimination of imp
symbol imp_intro        : ∀ (p : Prop) (q : Prop), P p ⇒ P q ⇒ P (imp p q)
symbol imp_elim         : ∀ (p : Prop) (q : Prop), P (imp p q) ⇒ P p ⇒ P q


theorem not_elimp : ∀ (A : Prop), P (not (not A)) ⇒ P A
proof
    intro A nnp
    refine or_elim A (not A) A _ _ _
    refine excl_mid A
    intro pa
    refine pa
    intro pna
    apply bot_elim
    refine nnp pna
qed

set builtin "P"     ≔ P
set builtin "T"     ≔ T
set builtin "eq"    ≔ eq
set builtin "eqind" ≔ eqind
set builtin "refl"  ≔ refl