// Triggers heavy memory consumption with trees
require open tests.OK.nat

symbol triangle : N ⇒ N
rule triangle (s &n) → (s &n) + (triangle &n)
 and triangle z      → z

compute triangle 300