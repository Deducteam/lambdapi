require open tests.OK.logic;
require open tests.OK.bool;

rule T bool ↪ B;

opaque symbol and_idempotent (a:B) : P (bool_and a a = a)
≔ begin
  assume a;
  refine bool_ind (λ a, bool_and a a = a) ?CT.[a] ?CF.[a] a
  {reflexivity}
  {reflexivity}
end;

// Same with a reduction rule.

rule bool_and $a $a ↪ $a;

opaque symbol and_idempotent_rw a : P (bool_and a a = a)
≔ begin
  assume a;
  reflexivity
end;
