symbol Prop: TYPE;
symbol ∧: Prop → Prop → Prop;
notation ∧ infix right 7;
constant symbol ⊤ : Prop;
constant symbol ⊥ : Prop;

sequential symbol doubles_in_and : Prop → Prop;

rule doubles_in_and ($p ∧ $q) when $p «[@∧] $q ↪ ⊤
with doubles_in_and ($p ∧ $q) ↪ doubles_in_and $q
with doubles_in_and $p ↪ ⊥;


assert p q r ⊢ doubles_in_and (p ∧ q ∧ r) ≡ ⊥;
assert p q r ⊢ doubles_in_and (q ∧ p ∧ r ∧ p) ≡ ⊤;
