require open tests.OK.boolean;
require open tests.OK.natural;
// require tests.OK.natural as Nat;
// open tests.OK.natural;

// Data type of natural numbers.

constant symbol I : TYPE;
constant symbol Z0 : I;
constant symbol Zpos : N → I;
constant symbol Zneg : N → I;

symbol * : I → I → I;
notation * infix right 22;

symbol + : I → I → I;
notation + infix right 24;

symbol — : I → I;
notation — prefix 24;


symbol _1 ≔ Zpos n1;
symbol _2 ≔ Zpos n2;
symbol _3 ≔ Zpos n3;
symbol _4 ≔ Zpos n4;
symbol _5 ≔ Zpos n5;
symbol _6 ≔ Zpos n6;
symbol _7 ≔ Zpos n7;
symbol _8 ≔ Zpos n8;
symbol _9 ≔ Zpos n9;
symbol _10 ≔ Zpos n10;
// enable printing of integers in decimal notation

builtin "int_zero" ≔ Z0;
builtin "int_positive" ≔ Zpos;
builtin "int_negative" ≔ Zneg;

// enable parsing of integers in decimal notation

builtin "0" ≔ Z0;
builtin "1" ≔ _1;
builtin "2" ≔ _2;
builtin "3" ≔ _3;
builtin "4" ≔ _4;
builtin "5" ≔ _5;
builtin "6" ≔ _6;
builtin "7" ≔ _7;
builtin "8" ≔ _8;
builtin "9" ≔ _9;
builtin "10" ≔ _10;

builtin "+" ≔ +;
builtin "*" ≔ *;
builtin "-" ≔ —;

// Test the support for natural builtin from a different module
symbol foo2 : N  ≔  tests.OK.natural.12 tests.OK.natural.+ tests.OK.natural.25;

symbol foo3 : I ≔ 12;