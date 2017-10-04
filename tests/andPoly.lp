Bool : Type.
Nat : Type.

True : Bool.
False : Bool.

0 : Nat.
S : Nat ⇒ Nat.

Bool_ : Nat ⇒ Type.
[]  Bool_ 0     → Bool.
[n] Bool_ (S n) → Bool ⇒ Bool_ n.

and : Bool ⇒ Bool ⇒ Bool.
[]  and False _ → False.
[x] and True  x → x.

and_ : n : Nat ⇒ Bool_ n.
[]      and_ 0             → True.
[x]     and_ (S 0)     x   → x.
[x y n] and_ (S (S n)) x y → and_ (S n) (and x y).

// Ici un and acceptant un nombre variable d'arguments qui type-check bien
and_ : n : Nat ⇒ Bool_ n.
[]      and_ 0         → True.
[x]     and_ (S 0)     → λx:Bool. x.
[x y n] and_ (S (S n)) → λx:Bool. λy:Bool. (and_ (S n) (and x y)).

e : n : Nat ⇒ Bool_ n ⇒ Bool_ n.

andb : n : Nat ⇒ Bool_ n.
[]      e 0 (andb 0        ) → True.
[x]     e 0 (andb (S 0) x  ) → x.
[x y n] e n (andb _     x y) → andb (S n) (and x y).
