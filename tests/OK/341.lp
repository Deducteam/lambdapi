symbol A : TYPE;
symbol f x : A ≔ x; // No warning
symbol a: A;
symbol g (x: A) : A ≔ a; // FIXME: should provide a warning
