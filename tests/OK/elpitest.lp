/* dune exec lambdapi check tests/OK/elpitest.lp */
require open tests.OK.logic;
require open tests.OK.bool;
require open tests.OK.nat;

flag "print_implicits" on; // default is off
flag "print_contexts" on; // default is off
flag "print_domains" on; // default is off
flag "print_meta_types" on; // default is off

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

instance symbol bool_eqdec : eqdec bool ≔ mk_eqdec eq_bool /* p */;
instance symbol nat_eqdec  : eqdec nat ≔ mk_eqdec eq_nat /* p */;
instance symbol pair_eqdec : Π i j, eqdec i → eqdec j → eqdec (pair i j);
  /* ≔ mk_eqdec eq_nat ; */

type λ b , true == b;
type λ n , 1 == n;
type λ n : T nat, λ b : T bool, mk_Pair 1 true == mk_Pair n b;

rule @== _ (@mk_eqdec _ $f /* _ */) ↪ $f;

compute true == true;
compute true == false;
compute 1 == 0;

// assert ⊢ eqop _ true false : B;
// elpi "tests/OK/elpitest.elpi" "main"
//  (Π x y , P (x = y) → P (y = x));
