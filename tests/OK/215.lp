require open tests.OK.nat;

symbol VectN : N → TYPE;
symbol nil: VectN 0;
symbol cons (n: N): N → VectN n → VectN (n + 1);

// [n] requires to be 0 to type
// Knowing that it is of type N is not enough
type let n ≔ 0 in cons n 0 nil;
