require tests.OK.prv

// Defining a rule with a foreign private symbol as head is forbidden
rule tests.OK.prv.f &X → &X
