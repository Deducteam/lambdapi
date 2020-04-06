require open tests.preuves_Ledein.Bool
require open tests.preuves_Ledein.Nat

// Boolean equality on N
symbol beq : N ⇒ N ⇒ B

rule beq 0         0      → true
 and beq (S &x) (S &y)    → beq &x &y
 and beq 0         (S _ ) → false
 and beq (S _ ) 0         → false

// Boolean less-than relation on N
symbol ble : N ⇒ N ⇒ B

rule ble 0         0      → false
 and ble 0         (S _ ) → true
 and ble (S &x) (S &y)    → ble &x &y
