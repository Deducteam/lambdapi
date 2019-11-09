require tests.OK.prv

symbol g : tests.OK.prv.A ⇒ tests.OK.prv.A

// Foreign private symbols are forbidden in right-hand-sides
rule g &X → tests.OK.prv.f &X
