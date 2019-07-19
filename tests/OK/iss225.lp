symbol T:TYPE
symbol a:T
symbol f:(T⇒T)⇒T
rule f (λx,&F[x]) → a
compute λx:T,f(λy,x) // does not return λx,a !