constant symbol A : TYPE;
private constant symbol B : TYPE;

// Private type B would escape its privacy and be exposed
symbol f : A → B;
