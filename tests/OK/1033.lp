// Test on the sequential reduction strategy
constant symbol I: TYPE;
constant symbol i: I;
constant symbol j: I;
sequential symbol k: I → I;
rule k i ↪ i
with k i ↪ j;

assert ⊢ k i ≡ i;
