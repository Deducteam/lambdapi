// let in RHS
symbol A : TYPE
symbol f : A ⇒ A
symbol g : A ⇒ A
rule f &x → let y ≔ g &x in y
symbol a : A
compute f a
