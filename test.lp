kind var X : Type;
kind var Y : Type;
kind var A : Type;

check λx:X.x : Πx:X.X;

check λx:X.λy:Y.x : X ⇒ Y ⇒ X;

kind var nat  : Type;
type var zero : nat;
type var succ : nat ⇒ nat;

kind var vec  : nat ⇒ Type;
type var nil  : vec zero;
type var cons : Πn:nat.A ⇒ vec n ⇒ vec (succ n);
