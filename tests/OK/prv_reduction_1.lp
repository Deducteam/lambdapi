symbol const A : TYPE
symbol Pair : TYPE

symbol pair : A ⇒ A ⇒ Pair

symbol private _pair : A ⇒ Pair

rule pair &X _ → _pair &X
