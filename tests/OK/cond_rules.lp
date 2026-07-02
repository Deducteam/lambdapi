symbol Prop: TYPE;
symbol ∧: Prop → Prop → Prop;
notation ∧ infix right 7;
constant symbol ⊤ : Prop;
constant symbol ⊥ : Prop;
symbol simp: Prop → Prop;
symbol simp1: Prop → Prop → Prop;

sequential symbol subterm: Prop → Prop → Prop;
rule subterm $p $p ↪ ⊤
with subterm $p ($p ∧ $q) ↪ ⊤
with subterm $p (_ ∧ $q) ↪ subterm $p $q
with subterm _ _ ↪ ⊥;

rule simp ($p ∧ ⊤) ↪ $p;
rule simp ($p ∧ $q ∧ $r) when subterm $p $r ≡ ⊤ ↪ simp1 $p $r;

assert p q r ⊢ (simp (p ∧ q ∧ p ∧ r)) ≡ simp1 p (p ∧ r);
