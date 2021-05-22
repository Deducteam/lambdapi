// Test simple coercions
constant symbol A : TYPE;
constant symbol a : A;
constant symbol B : TYPE;
constant symbol a2b : A → B;
constant symbol f : B → B;

coercion "a2b" a2b : A → B on 1;
assert ⊢ f a ≡ f (a2b a);

// The coercion on codes, allow to not write the decoding function El
constant symbol Set : TYPE;
injective symbol El : Set → TYPE;
constant symbol nat : Set;
coercion "decode" El : Set → TYPE on 1;
assert ⊢ nat → Set ≡ El nat → Set;

// Apply coercion in symbol definition
//constant symbol succ : nat → nat;
constant symbol z : nat;
constant symbol succ : nat → nat;
