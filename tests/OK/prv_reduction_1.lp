symbol const A : TYPE
symbol Pair : TYPE

symbol pair : A ⇒ A ⇒ Pair

private symbol _pair : A ⇒ Pair

rule pair &X _ → _pair &X
