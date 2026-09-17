symbol Prop: TYPE;
symbol ∧: Prop → Prop → Prop;
notation ∧ infix right 7;
constant symbol ⊤ : Prop;
constant symbol ⊥ : Prop;

sequential symbol doubles_in_and : Prop → Prop;
sequential symbol occurs_in_and : Prop → Prop → Prop;

rule doubles_in_and ($p ∧ $q) when occurs_in_and $p $q ≡ ⊤ ↪ ⊤
with doubles_in_and (_ ∧ $q) ↪ doubles_in_and $q
with doubles_in_and _ ↪ ⊥;

rule occurs_in_and $p $p ↪ ⊤
with occurs_in_and $p ($p ∧ _) ↪ ⊤
with occurs_in_and $p (_ ∧ $q) ↪ occurs_in_and $p $q
with occurs_in_and _ _ ↪ ⊥;

assert p q r ⊢ doubles_in_and (p ∧ q ∧ r) ≡ ⊥;
assert p q r ⊢ doubles_in_and (p ∧ q ∧ p ∧ r) ≡ ⊤;
