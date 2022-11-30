constant symbol T : TYPE;
constant symbol U : TYPE;

symbol fst : T → U → T ≔ λ x _, x;
symbol snd : T → U → U ≔ λ _ x, x;

opaque symbol trivial : T → T → T → T
≔ begin
  assume _ _ x;
  refine x
end;
