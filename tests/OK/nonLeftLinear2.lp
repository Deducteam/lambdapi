// Tests correctness of rewriting engine on left non linear rules
require open tests.OK.nat;
require open tests.OK.bool;

symbol eq_nl : N → N → B;

rule eq_nl (s $x) (s $x) ↪ true
with eq_nl 0      0      ↪ true
with eq_nl (s _)  0      ↪ false
with eq_nl 0      (s _)  ↪ false;
assert ⊢ eq_nl 3 3 ≡ true;

symbol f : N → N → N → B;
rule f $x $x _  ↪ true
with f _  $x $x ↪ false;
assert ⊢ f 4 4 11 ≡ true;
assert ⊢ f 4 11 11 ≡ false;

symbol g : N → N → B;
rule g $x $x ↪ true;
assert ⊢ g 4 4 ≡ true;

symbol h : N → N → N → B;
rule h $x $x $x ↪ true
with h $x 0 (s $x) ↪ false;
assert ⊢ h 3 3 3 ≡ true;
assert ⊢ h 2 0 3 ≡ false;
