symbol Prop: TYPE;
symbol ∧: Prop → Prop → Prop;
notation ∧ infix right 7;
constant symbol ⊤ : Prop;
constant symbol ⊥ : Prop;
symbol simp: Prop → Prop;
symbol simp1: Prop → Prop → Prop;

sequential symbol sub_all: Prop → Prop → Prop;
rule sub_all $p $p ↪ ⊤
with sub_all $p ($p ∧ $q) ↪ ⊤
with sub_all $p (_ ∧ $q) ↪ sub_all $p $q
with sub_all _ _ ↪ ⊥;

rule simp ($p ∧ ⊤) ↪ $p;
rule simp ($p ∧ $q ∧ $r) when sub_all $p $r ≡ ⊤ ↪ simp1 $p $r;

assert p q r ⊢ simp (p ∧ q ∧ p ∧ r) ≡ simp1 p (p ∧ r);
