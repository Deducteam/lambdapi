// Test that infix operators are considered as terms by commands
symbol A: TYPE;
symbol +: A → A → A;
notation + infix 5;
type (+);
