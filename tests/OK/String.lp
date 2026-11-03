// builtin string type

require open tests.OK.Set;

constant symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule τ string ↪ String;
