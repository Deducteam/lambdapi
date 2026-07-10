// A tactic failing mid-proof: the error must carry the proof state
// (hypotheses, separator, goals) as its description (see proof_state.ml).
constant symbol Prop : TYPE;
injective symbol π : Prop → TYPE;
constant symbol A : Prop;
constant symbol B : Prop;
symbol imp : Prop → Prop → Prop;
rule π (imp $a $b) ↪ π $a → π $b;
opaque symbol demo : π (imp A (imp B A)) ≔
begin
  assume a b;
  fail
end;
