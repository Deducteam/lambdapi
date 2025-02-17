constant symbol String : TYPE;
builtin "String" ≔ String;

type "hello world!";

compute "hello world!";

assert ⊢ "a" : String;

assert ⊢ "a" ≡ "a";

assertnot ⊢ "a" ≡ "b";
