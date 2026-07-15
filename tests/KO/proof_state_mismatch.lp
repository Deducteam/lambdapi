// A subproof-count mismatch is only detected after the tactic ran: the error
// must carry the proof state before AND after it (see proof_state.ml).
constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "P" ≔ π;
inductive N : TYPE ≔ | z : N | succ : N → N;
symbol Q : N → Prop;
opaque symbol demo : Π n, π (Q n) ≔
begin
  induction
end;
