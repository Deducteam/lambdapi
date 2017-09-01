kind var X : Type;
kind var Y : Type;

check λx:X.x : Πx:X.X;

check λx:X.λy:Y.x : Πx:X.Πy:Y.X;

kind var nat  : Type;
type var zero : nat;
type var succ : nat ⇒ nat;
