// Data type of booleans.

constant symbol B : TYPE;

constant symbol true  : B;
constant symbol false : B;

// Boolean negation.

symbol bool_neg : B → B;

rule bool_neg true  ↪ false
with bool_neg false ↪ true;

// Boolean disjunction.

symbol bool_or : B → B → B;

rule bool_or true  _     ↪ true
with bool_or false $b    ↪ $b
with bool_or _     true  ↪ true
with bool_or $b    false ↪ $b;

// Boolean conjunction.

symbol bool_and : B → B → B;

rule bool_and true  $b    ↪ $b
with bool_and false _     ↪ false
with bool_and $b    true  ↪ $b
with bool_and _     false ↪ false;

// More connectives.

symbol bool_impl a b ≔
  bool_or b (bool_neg a);

symbol bool_xor a b ≔
  let a_and_not_b ≔ bool_and a (bool_neg b) in
  let b_and_not_a ≔ bool_and b (bool_neg a) in
  bool_or a_and_not_b b_and_not_a;
