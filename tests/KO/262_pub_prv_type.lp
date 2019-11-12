symbol const A : TYPE
private symbol const B : TYPE

// Private type B would escape its privacy and be exposed
symbol f : A ⇒ B
