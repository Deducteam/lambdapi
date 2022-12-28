symbol SortK : TYPE;

symbol δ : SortK → TYPE;

symbol SortInt : SortK;
symbol zero : δ SortInt;
symbol succ : δ SortInt → δ SortInt;

builtin "0" ≔ zero;
builtin "+1" ≔ succ;

symbol A : δ SortInt;
rule A ↪ 9223372036854775808;
