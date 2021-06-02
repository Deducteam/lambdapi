constant symbol Set:TYPE;
constant symbol nat:Set;

injective symbol τ:Set → TYPE;
constant symbol z:τ nat;

symbol f a:τ a → τ a;

type (λ {a}, λ x, f a x) z;
