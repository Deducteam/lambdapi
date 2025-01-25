require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Bool;

inductive ℕ : TYPE ≔
| O : ℕ
| +1 : ℕ → ℕ; notation +1 postfix 100;

constant symbol nat : Set;

rule τ nat ↪ ℕ;

symbol + : ℕ → ℕ → ℕ; notation + infix 20;
symbol × : ℕ → ℕ → ℕ; notation + infix 20;

// Enabling decimal notation

symbol n1 ≔ O +1;
symbol n2 ≔ n1 +1;
symbol n3 ≔ n2 +1;
symbol n4 ≔ n3 +1;
symbol n5 ≔ n4 +1;
symbol n6 ≔ n5 +1;
symbol n7 ≔ n6 +1;
symbol n8 ≔ n7 +1;
symbol n9 ≔ n8 +1;
symbol n10 ≔ n9 +1;

builtin "0"  ≔ O;
builtin "1" ≔ n1;
builtin "2" ≔ n2;
builtin "3" ≔ n3;
builtin "4" ≔ n4;
builtin "5" ≔ n5;
builtin "6" ≔ n6;
builtin "7" ≔ n7;
builtin "8" ≔ n8;
builtin "9" ≔ n9;
builtin "10" ≔ n10;

builtin "+" ≔ +;
builtin "*" ≔ ×;

symbol forty_two ≔ 42;
