symbol A:TYPE;
symbol a:A;

symbol +:A → A → A; notation + infix right 10;

assert ⊢ (+) : A → A → A;
assert ⊢ (+) a : A → A;
assert ⊢ @+ : A → A → A;
assert ⊢ @+ a : A → A;
assert ⊢ (@+ a a) + a : A;

symbol * {_:A} : A → A → A; notation * infix right 10;

assert ⊢ (*) : A → A → A;
assert ⊢ (*) a : A → A;
assert ⊢ @* : A → A → A → A;
assert ⊢ @* a : A → A → A;
assert ⊢ (@* _ a a) * a : A;

symbol f : (A → A → A) → A;

assert ⊢ f (+) : A;
assert ⊢ f @+ : A;

assert ⊢ f (*) : A;
assert ⊢ f (@* _) : A;
