symbol const A : TYPE
symbol Pair : TYPE

symbol pair : A ⇒ A ⇒ Pair

// Use example: public [pair] reduces to private [_pair]
private symbol _pair : A ⇒ Pair

rule pair &X _ → _pair &X
