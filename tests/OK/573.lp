// test matching on type annotations in abstractions/products

constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;

constant symbol prop : Set;
symbol Prop ≔ τ prop;
injective symbol π : Prop → TYPE;

constant symbol ∀ {a} : (τ a → Prop) → Prop;
set notation ∀ quantifier;

set unif_rule π $p ≡ Π x:$t, π $q[x] ↪ [ $p ≡ `∀ x:$t, $q[x] ];
