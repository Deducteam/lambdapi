symbol Prop : TYPE;
injective symbol π: Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "Prf" ≔ π;

symbol context: TYPE;
symbol □ : context;
associative commutative symbol ∙ : context → context → context;
notation ∙ infix right 1;

symbol γ: context → context;
rule □ ∙  $H ↪ $H;

inductive valid1: context → TYPE ≔
| R1 H1 H2 : valid1 (H1 ∙ H2) → valid1 H2;

inductive valid2: context → TYPE ≔
| R2 H1 H2 : valid2 (H1 ∙ H2) → valid2 H1;

inductive valid3: context → TYPE ≔
| R3 P H : valid3 (H ∙ γ P) → valid3 H;

inductive valid4: context → TYPE ≔
| R4 P H : valid4 (γ P ∙ H) → valid4 H;
