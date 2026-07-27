require open tests.OK.Eq tests.OK.HOL;

symbol funExt [a b] (f g : τ (a ⤳ b)) : (Π x, π(f x = g x)) → π(f = g);
