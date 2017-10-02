type  : Type.
arr   : type ⇒ type ⇒ type.
e     : type ⇒ Type.
[a b] e (arr a b) → e a ⇒ e b.

N : type.
z : e N.
s : e N ⇒ e N.

numeral : Type.
[] numeral → A:type ⇒ (e A ⇒ e A) ⇒ (e A ⇒ e A).

0 : numeral.
1 : numeral.
2 : numeral.
3 : numeral.
[] 0 → λA:type.λf:(e A ⇒ e A).λx:(e A).x.
[] 1 → λA:type.λf:(e A ⇒ e A).f.
[] 2 → λA:type.λf:(e A ⇒ e A).λx:(e A).f (f x).
[] 3 → λA:type.λf:(e A ⇒ e A).λx:(e A).f (f (f x)).

plus : numeral ⇒ numeral ⇒ numeral.
[] plus → λm:numeral.λn:numeral.λA:type.λf:(e A ⇒ e A).λx:(e A).m A f (n A f x).

times : numeral ⇒ numeral ⇒ numeral.
[] times → λm:numeral.λn:numeral.λA:type.λf:(e A ⇒ e A).λx:(e A).m A (n A f) x.

power : numeral ⇒ numeral ⇒ numeral.
[] power → λm:numeral.λn:numeral.λA:type.n (arr A A) (m A).

4 : numeral.
[] 4 → plus 2 2.

5 : numeral.
[] 5 → plus 2 3.

#EVAL power 2 (times 4 5).
#EVAL power 2 (times 5 4).

#CONV λx:numeral.x, λy:numeral.y.
#CONV times 4 5, times 5 4.

#EVAL power 2 (times 4 5).
#EVAL power 2 (times 5 4).

// FIXME (loops)
//#CONV power 2 (times 4 5), power 2 (times 5 4).
