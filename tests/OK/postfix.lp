require open tests.OK.natural;
symbol ! (_: N): N;
notation ! postfix 9;

rule (s $n) ! ↪ (s $n) × $n !;
rule z ! ↪ (s z);

assert ⊢ 3 ! ≡ 6;
