require open tests.OK.Set;

constant symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule τ string ↪ String;

type "hello world!";

compute "hello world!";

assert ⊢ "a" : String;

assert ⊢ "a" ≡ "a";

assertnot ⊢ "a" ≡ "b";
