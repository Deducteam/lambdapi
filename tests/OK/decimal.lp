require open tests.OK.Nat;

assert ⊢ 001009 + 11 ≡ 0 + 01020;

require open tests.OK.Pos;

assert ⊢ add 001009 11 ≡ 01020;

require open tests.OK.Z;

assert ⊢ 1 : ℤ;

assert ⊢ tests.OK.Nat.1 : ℕ;
