Set  : Type.
Prop : Type.

prf : Prop ⇒ Type.

forall : (Set ⇒ Prop) ⇒ Prop.
imp    : Prop ⇒ Prop ⇒ Prop.

[f]   prf (forall f) → x:Set ⇒ prf (f x).
[A B] prf (imp A B)  → prf A ⇒ prf B.

False : Prop.
not : Prop ⇒ Prop.

[] not → λA:Prop.imp A False.

in : Set ⇒ Set ⇒ Prop.
empty : Set.
empty_ax : prf (forall (λx:Set.not (in x empty))).

leq : Set ⇒ Set ⇒ Prop.
min : Set ⇒ Set ⇒ Prop.

min_ax1 : prf (
  forall (λS:Set.
  forall (λx:Set.
  forall (λy:Set.
 	imp (min x S) (imp (in y S) (leq x y)) )))).

min_ax2 : prf (
  forall (λS:Set.
  forall (λx:Set.
  imp (min x S) (in x S)))).

stmt : Prop.
[] stmt → forall (λx:Set. not (min x empty)).

theorem : prf stmt.
// FIXME (typing / inference)
//[] theorem → λx:Set. λp:Set. (empty_ax x) (min_ax2 empty x p).
