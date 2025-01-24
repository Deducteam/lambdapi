symbol Set:TYPE;
injective symbol τ:Set → TYPE;
symbol ℕ:TYPE;
symbol O:ℕ;
symbol 𝑰 [a]: ℕ → τ a;

symbol code_S' : Set;
symbol S' ≔ τ code_S';
//print S';
//debug +uv;
symbol a':S' ≔ 𝑰 O;
//debug -uv;

private symbol code_S : Set;
private symbol S ≔ τ code_S;
//print S;
//debug +uv;
private symbol a: S ≔ 𝑰 O;
