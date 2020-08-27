symbol A : TYPE.
symbol a: A.
symbol f: A → A.

symbol g: Π(x:A), A.

definition id : A → A ≔ λ(x: A), x.
definition id2 (x: A) ≔ x.

rule g $x ↪ f $x.
