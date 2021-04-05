// test type inference in the case of an application (t u)
// where the type of t is not a product (yet)

constant symbol Prop : TYPE;
injective symbol π : Prop → TYPE;

constant symbol ∧ : Prop → Prop → Prop;
notation ∧ infix left 5;
rule π ($A ∧ $B) ↪ Π P, (π $A → π $B → π P) → π P;

constant symbol and_i A B : π A → π B → π (A ∧ B);
constant symbol and_eg A B : π (A ∧ B) → π A;
constant symbol and_ed A B : π (A ∧ B) → π B;

constant symbol ⇒ : Prop → Prop → Prop;
notation ⇒ infix right 6;
rule π ($A ⇒ $B) ↪ π $A → π $B;

constant symbol imp_e A B : π (A ⇒ B) → π A → π B;

symbol P : Prop;
symbol R : Prop;

type λ H: π((P ⇒ R) ∧ (R ⇒ P)), λ Hr: π R, and_ed _ _ H Hr;
