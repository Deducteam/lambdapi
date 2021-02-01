require open tests.OK.logic;
require open tests.OK.nat;

set prover "Alt-Ergo";
set prover_timeout 2;


opaque symbol tautology : Π (a : Prop), P a → P a
≔ begin
    assume a pa;
    why3;
end;

opaque symbol thm_and1 : Π (a b : Prop), P ({|and|} a b) → P a
≔ begin
    assume a b pab;
    why3;
end;


opaque symbol thm_and2 : Π (a b : Prop), P ({|and|} a b) → P b
≔ begin
    assume a b pab;
    why3;
end;

opaque symbol excluded_middle : Π (a : Prop), P (or a (not a))
≔ begin
    assume a;
    why3;
end;

opaque symbol thm_or1 : Π (a b : Prop), P a → P (or a b)
≔ begin
    assume a b pa;
    why3;
end;

opaque symbol thm_or2 : Π (a b : Prop), P b → P (or a b)
≔ begin
    assume a b pb;
    why3;
end;

opaque symbol thm_imp : Π (a b : Prop), P (imp a b) → P a → P b
≔ begin
    assume a b pab pa;
    why3;
end;
