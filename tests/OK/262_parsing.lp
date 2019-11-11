// Test parsing of local and private keywords
// Define several constants to be used by other tests
symbol const A : TYPE

local symbol f : A ⇒ A
private symbol g : A ⇒ A

local definition fdouble x ≔ f (f x)
private definition gdouble x ≔ g (g x)

// Mixing private, local and public
definition fog x ≔ f (g x) // Private and local
symbol h : A ⇒ A
definition fogoh x ≔ f (g (h x)) // Public, private, local
