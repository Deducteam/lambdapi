symbol Set: TYPE;
symbol Prop: TYPE;
injective symbol τ: Set → TYPE;
injective symbol π: Prop → TYPE;
require open tests.OK.Tactic;

constant symbol OK: Prop;
symbol isOK [a:Set] (x:τ a): π OK;

print #assume;
print #apply;

symbol test [a:Set] (x: τ a) (y: τ a): π OK ≔
begin
  assume a;
  eval (#assume "x" (λ x1,
    #print "assume1" & (#assume "x" (λ x2,
      #print "assume2" & #apply (isOK x1)))));
end;
