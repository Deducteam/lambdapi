require open tests.OK.logic;
require open tests.OK.natural;

prover "Alt-Ergo";
prover_timeout 2;

opaque symbol tautology : Π (a : Prop), P a → P a
≔ begin
    why3;
end;

opaque symbol thm_and1 : Π (a b : Prop), P ({|and|} a b) → P a
≔ begin
    why3;
end;


opaque symbol thm_and2 : Π (a b : Prop), P ({|and|} a b) → P b
≔ begin
    why3;
end;

opaque symbol excluded_middle : Π (a : Prop), P (or a (not a))
≔ begin
    why3;
end;

opaque symbol thm_or1 : Π (a b : Prop), P a → P (or a b)
≔ begin
    why3;
end;

opaque symbol thm_or2 : Π (a b : Prop), P b → P (or a b)
≔ begin
    why3;
end;

opaque symbol thm_imp : Π (a b : Prop), P (imp a b) → P a → P b
≔ begin
    why3;
end;
