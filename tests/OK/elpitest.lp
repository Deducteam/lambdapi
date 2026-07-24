/* dune exec lambdapi check tests/OK/elpitest.lp */
require open tests.OK.logic;
require open tests.OK.boolean;

flag "print_implicits" on; // default is off
flag "print_contexts" on; // default is off
flag "print_domains" on; // default is off

constant typeclass symbol eqdec : U → TYPE;
constant symbol mk_eqdec [i] :
  Π (f : T i → T i → B),
  // (Π (x y : T i), P ({|and|} (imp (x = y) (f x y = true))(imp (f x y = true) (x = y))))  →
  eqdec i;

symbol == [i:U] [j:eqdec i] : T i → T i → B;
notation == infix 1;

/* extra stdlib */
symbol eq_bool : B → B → B ≔ λ b1 b2, bool_neg (bool_xor b1 b2);
symbol Pair : U → U → TYPE;
symbol mk_Pair [i] [j] : T i → T j → Pair i j;
symbol pair : U → U → U;
rule T (pair $i $j) ↪ Pair $i $j;
symbol fst [i j] : Pair i j → T i;
rule @fst $i $j (@mk_Pair $i $j $x _) ↪ $x;
symbol snd [i j] : Pair i j → T j;
rule @snd $i $j (@mk_Pair $i $j _ $y) ↪ $y;
symbol eq_pair [i j] (eqi : T i → T i → B) (eqj : T j → T j → B) (p1 p2 : Pair i j): B ≔
  bool_and (eqi (@fst i j p1) (@fst i j p2)) (eqj (@snd i j p1) (@snd i j p2));


instance symbol bool_eqdec : eqdec bool ≔ mk_eqdec eq_bool /* p */;
instance symbol nat_eqdec  : eqdec nat ≔ mk_eqdec eq_nat /* p */;
//type _;
//type λ x , true == x;
type U;
type pair;
type λ i j (deci : eqdec i) (decj : eqdec j), mk_eqdec (@eq_pair i j (==) (==));
symbol test ≔ λ n, n == 1;
instance symbol pair_eqdec : Π i j, eqdec i → eqdec j → eqdec (pair i j) ≔
  λ i j deci decj, mk_eqdec (@eq_pair i j (==) (==));

type λ x , true == x;
type λ n , 1 == n;
type λ n : T nat, λ B0 : B, mk_Pair 1 B0 == mk_Pair n B0;

rule @== _ (@mk_eqdec _ $f) ↪ $f;

compute true == true;
compute true == false; 
compute 1 == 0;
compute mk_Pair 1 true == mk_Pair 1 true;

print test;
print pair_eqdec;

// assert ⊢ eqop _ true false : B;
// elpi "tests/OK/elpitest.elpi" "main"
//  (Π x y , P (x = y) → P (y = x));
