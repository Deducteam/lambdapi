symbol Prop: TYPE;
builtin "Prop" ≔ Prop;

injective symbol π: Prop → TYPE;
builtin "Prf" ≔ π;

symbol Set: TYPE;
builtin "Set" ≔ Set;

injective symbol τ: Set → TYPE;
builtin "El" ≔ τ;

require open tests.OK.Tactic;

constant symbol OK: Prop;
symbol isOK [a:Set] (x:τ a): π OK;

symbol test [a:Set] (x: τ a) (y: τ a): π OK ≔
begin
  assume a;
  eval #assume "x" (λ x1, #assume "x" (λ x2, #apply (isOK x1)));
end;
