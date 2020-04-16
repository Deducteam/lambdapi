constant symbol A : TYPE

private symbol f : A → A
symbol g : A → A

// The private [f] would become public with fog
definition fog x ≔ f (g x)
