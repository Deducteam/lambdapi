symbol Set: TYPE;
symbol Prop: TYPE;
injective symbol τ: Set → TYPE;
injective symbol π: Prop → TYPE;
require open tests.OK.Tactic;

constant symbol OK: Prop;
symbol isOK: π OK;

symbol test [T:Set] (a: τ T) (b: τ T): π OK ≔
begin
  assume T;
  eval (#assume "x" (λ (a1: τ T),
                     #print "assume1" &
                                      (#assume "x" (λ (a2: τ T),
                       #print "assume2" &
                                        #apply isOK))));
end;
