kind var X : Type;

check λx:X.x : Πx:X.X;

kind var nat  : Type;
type var zero : nat;
type var succ : Πn:nat.nat;
