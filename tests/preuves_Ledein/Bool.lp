require open tests.preuves_Ledein.notation

// Induction principle on B.
symbol bool_ind : ∀ (P:B⇒Prop), π(P true) ⇒ π(P false) ⇒ ∀b, π(P b)
rule bool_ind _ &t _  true  → &t
 and bool_ind _ _  &f false → &f
                              
// Negation
symbol not : B ⇒ B
rule not true  → false
 and not false → true

// Disjunction
symbol or : B ⇒ B ⇒ B
set infix left 6 "|" ≔ or
rule true | _  → true
 and _  | true → true
 and false | &b → &b
 and &b | false → &b

// Conjunction
symbol {|and|} : B ⇒ B ⇒ B
set infix left 7 "^" ≔ {|and|}
rule true ^ &b → &b
 and &b ^ true → &b
 and false ^ _  → false
 and _  ^ false → false
