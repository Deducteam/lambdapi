// check warnings on unused parameters in symbol declarations

symbol A : TYPE;
symbol f x : A ≔ x; // should not generate a warning
symbol B : A → TYPE;
symbol a : A;
symbol g (x:A) : A ≔ a; // should generate a warning
symbol h x : Π y:A,A ≔ λ _,x; // should generate a warning
symbol i x : (Π y:A, A) → A ≔ λ _,x; // should generate a warning
symbol j (x:A) : (λ _, A) x ≔ a; // should not generate a warning

symbol Set : TYPE;
symbol τ : Set → TYPE;
symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
symbol π : Prop → TYPE;
builtin "P" ≔ π;

(a:Set) inductive L : TYPE ≔
| nil  : L a
| cons : τ a → L a → L a; // should not generate a warning
