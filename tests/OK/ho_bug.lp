symbol T:TYPE
symbol a:T
symbol f:(T⇒T)⇒T
rule f (λx,&F[x]) → a
compute λz,λx:T,f(λy,z) // does not return λx,a !