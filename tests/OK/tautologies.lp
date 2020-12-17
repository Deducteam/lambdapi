require open tests.OK.logic
require open tests.OK.bool

// [Π a, bool_and a a = a]
opaque symbol and_idempotent : Πa, P (eq bool (bool_and a a) a) ≔
begin
  assume a
  refine bool_ind (λa, eq bool (bool_and a a) a) ?CT[a] ?CF[a] a
  reflexivity
  reflexivity
end

// Same with a reduction rule.

rule bool_and $a $a ↪ $a

opaque symbol and_idempotent_rw : Πa, P (eq bool (bool_and a a) a) ≔
begin
  assume a
  reflexivity
end
