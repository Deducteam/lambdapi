require open tests.OK.prv

symbol g : A ⇒ A

// Allowed to use private symbol f in lhs of rewrite rule
rule g (f &X) → &X
