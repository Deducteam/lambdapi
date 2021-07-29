// See https://github.com/Deducteam/lambdapi/issues/725
// This file ensures that implicits arguments are correctly detected, even
// when a let in declaration appears between arguments.

symbol Prop: TYPE;
symbol Set: TYPE;
symbol El: Set → TYPE;
symbol psub (t: Set) (_: El t → Prop): Set;

symbol foo: Π {T: Set} {S_pred : El T → Prop},
            let S : Set ≔ psub T S_pred in // The let in between the arguments
            Π {e: El S}, El S ≔
  λ{T:Set} {S_pred: El T → Prop},
  let S : Set ≔ psub T S_pred in
  λ {e: El S}, e;

constant symbol i: Set;
constant symbol i_pred: El i → Prop;
symbol x : El (psub i i_pred);
assert ⊢ foo {i} {i_pred} {x} ≡ x;
