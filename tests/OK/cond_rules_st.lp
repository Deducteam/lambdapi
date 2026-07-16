require open tests.OK.List;

symbol ∧: Prop → Prop → Prop;
notation ∧ infix right 7;
constant symbol ⊤ : Prop;
constant symbol ⊥ : Prop;

constant symbol o: Set;
rule τ o ↪ Prop;

symbol #find_doubles (T:Set) (op: τ T → τ T → τ T) (u: τ T) (p: τ T) (d: τ T) (b m a: τ T): Prop;

sequential symbol simpl: Prop → Prop;
rule simpl $p when #find_doubles o @∧ ⊤ $p $d $b $m $a ↪ $b ∧ $d ∧ $m ∧ $a;
rule simpl $p ↪ $p;

//compute (λ p q r, simpl (p ∧ q ∧ r ∧ p));

//assert p q r ⊢ simpl (p ∧ q ∧ r) ≡ p ∧ q ∧ r;
assert p q r ⊢ simpl (q ∧ p ∧ r ∧ p) ≡ p;
