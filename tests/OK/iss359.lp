// Test that infix operators are considered as terms by commands
symbol A: TYPE;
symbol f: A → A → A;
set infix 5 "+" ≔ f;
type +;
