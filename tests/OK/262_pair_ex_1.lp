constant symbol A : TYPE;
symbol Pair : TYPE;

symbol pair : A → A → Pair;

// Use example: public [pair] reduces to protected [_pair]
protected symbol _pair : A → Pair;

rule pair $X _ ↪ _pair $X;
