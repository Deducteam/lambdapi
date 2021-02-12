// test escaped identifiers
symbol {| |}:TYPE;
symbol {|}|}:TYPE;
symbol {|||}:TYPE;
symbol {|a.}|_|_}}|||}:TYPE;
symbol A:TYPE;
assert ⊢ A ≡ {|A|};
