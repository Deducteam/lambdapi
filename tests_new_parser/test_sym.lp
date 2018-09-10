require nothing

// Some things
symbol const test : TYPE
symbol injective succ : TYPE
symbol blop : TYPE

rule Plus Zero &n → &n

rule Plus (Succ &n) &m → Succ (Plus &n &m)
 and Mult Zero      _  → Zero
 and Mult (Succ &n) &m → Plus &m (Mult &n &m)

symbol none : Blop
