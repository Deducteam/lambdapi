constant symbol A : TYPE;

symbol f : A → A;
private symbol z : A;

// z would escape its scope
rule f _ ↪ z;
