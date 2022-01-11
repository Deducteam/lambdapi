// test that builtin 0 can be used without defining buitin +1
symbol N : TYPE;
symbol zero : N; builtin "0" ≔ zero;
print zero;
