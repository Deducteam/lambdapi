require open tests.OK.Set tests.OK.Prop tests.OK.Nat tests.OK.List;

symbol sample_1 (list : 𝕃 nat) : π ⊤ ≔
begin
  induction
    { apply ⊤ᵢ }
    { assume x l ih; apply ih }
end;
