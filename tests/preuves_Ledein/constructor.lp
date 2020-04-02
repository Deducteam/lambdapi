// Property type
constant symbol Prop : TYPE
injective symbol P : Prop ⇒ TYPE
set declared "π"
definition π ≔ P
set builtin "P" ≔ π

// Set type
constant symbol Set : TYPE
injective symbol T : Set ⇒ TYPE
set declared "τ"
definition τ ≔ T
set builtin "T" ≔ τ

// Boolean type
constant symbol bool : Set
definition B ≔ τ bool
rule T bool       → B
constant symbol true : B
constant symbol false : B
                        
// Nat type
constant symbol nat  : Set
definition N ≔ τ nat
rule T nat        → N
constant symbol zero : N
constant symbol succ : N ⇒ N
set builtin "0"  ≔ zero
set builtin "+1" ≔ succ
