constant symbol Typ : TYPE;

injective symbol η : Typ → TYPE;

constant symbol ⇒ : Typ → Typ → Typ;
notation ⇒ infix right 1.0;
rule η ($a ⇒ $b) ↪ η $a → η $b;

constant symbol + ['a : Typ] : η 'a → η 'a;
constant symbol Int: Typ;

symbol problem ≔ + (λ (x : η Int), + x);
