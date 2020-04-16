// Test parsing of protectedwith private keywords
// Define several constants to be used by other tests
constant symbol A : TYPE

private symbol f : A → A
protected symbol g : A → A

private definition fdouble x ≔ f (f x)
protected definition gdouble x ≔ g (g x)

// Mixing public, protectedwith private: if the head is private, so is the
// rest
private definition fog x ≔ f (g x) // Privatewith protected
symbol h : A → A
private definition fogoh x ≔ f (g (h x)) // Public, private, protected

// Rewriting rules from private symbols to private symbols are allowed
private symbol a : A
rule f _ ↪ a
