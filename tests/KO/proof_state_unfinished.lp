// Reaching `end` with goals remaining: the error must carry the remaining
// proof state as its description (see proof_state.ml).
constant symbol Prop : TYPE;
injective symbol π : Prop → TYPE;
constant symbol A : Prop;
symbol imp : Prop → Prop → Prop;
rule π (imp $a $b) ↪ π $a → π $b;
opaque symbol demo : π (imp A A) ≔
begin
  assume a
end;
