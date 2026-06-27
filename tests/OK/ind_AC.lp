symbol Prop : TYPE;
injective symbol π: Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "P" ≔ π;

symbol context: TYPE;
symbol □ : context;
associative commutative symbol ∙ : context → context → context;

notation ∙ infix right 1;

symbol γ: Prop → context;
rule □ ∙  $H ↪ $H;

inductive valid1: context → TYPE ≔
| R1 h1 h2 : valid1 (h1 ∙ h2) → valid1 h2;

inductive valid2: context → TYPE ≔
| R2 h1 h2 : valid2 (h1 ∙ h2) → valid2 h1;

inductive valid3: context → TYPE ≔
| R3 p h : valid3 (h ∙ γ p) → valid3 h;

inductive valid4: context → TYPE ≔
| R4 p h : valid4 (γ p ∙ h) → valid4 h;
