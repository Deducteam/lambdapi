// builtin type of strings

require open tests.OK.Set;

constant symbol String : TYPE;
builtin "String" ≔ String;

constant symbol string : Set;
rule τ string ↪ String;

constant symbol gen_id : String → String;
builtin "gen_id" ≔ gen_id;
