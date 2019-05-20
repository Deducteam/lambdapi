require open tests.OK.nat

symbol id : N ⇒ N
rule id &x → &x

symbol add' : N ⇒ N ⇒ N
rule add' 0 → id
 and add' (s &x) &y → &x + &y + 1

assert add' 0 0 ≡ 0