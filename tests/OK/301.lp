constant symbol U : TYPE
constant symbol u : U
symbol Ux : U ⇒ TYPE
rule Ux _ → U
constant symbol hx : ∀ (x : U), (Ux x ⇒ U) ⇒ U
symbol g : U ⇒ U
set debug +su
set flag "print_domains" on
rule g &i → hx &i (λ_, u)
