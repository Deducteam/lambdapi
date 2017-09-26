type  : Type.
arr   : type ⇒ type ⇒ type.
e     : type ⇒ Type.
[a b] e (arr a b) → e a ⇒ e b.

N : type.
z : e N.
s : e N ⇒ e N.

numeral : Type.
[] numeral → A:type ⇒ (e A ⇒ e A) ⇒ (e A ⇒ e A).

zero  : numeral.
one   : numeral.
two   : numeral.
three : numeral.
[] zero  → λA:type.λf:(e A ⇒ e A).λx:(e A).x.
[] one   → λA:type.λf:(e A ⇒ e A).f.
[] two   → λA:type.λf:(e A ⇒ e A).λx:(e A).f (f x).
[] three → λA:type.λf:(e A ⇒ e A).λx:(e A).f (f (f x)).

plus : numeral ⇒ numeral ⇒ numeral.
[] plus → λm:numeral.λn:numeral.λA:type.λf:(e A ⇒ e A).λx:(e A).m A f (n A f x).

times : numeral ⇒ numeral ⇒ numeral.
[] times → λm:numeral.λn:numeral.λA:type.λf:(e A ⇒ e A).λx:(e A).m A (n A f) x.

power : numeral ⇒ numeral ⇒ numeral.
[] power → λm:numeral.λn:numeral.λA:type.n (arr A A) (m A).

four : numeral.
[] four → plus two two.

five : numeral.
[] five → plus two three.

#EVAL power two (times four five).
#EVAL power two (times five four).

#CONV λx:numeral.x, λy:numeral.y.
#CONV times four five, times five four.
//#CONV power two (times four five), power two (times five four).
