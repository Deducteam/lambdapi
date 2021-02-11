// test escaped identifiers in paths
require open {|tests|}.OK.{|a b|}.{|escape file|};
assert ⊢ {|tests|}.OK.{|a b|}.{|escape file|}.A
           ≡ tests.OK.{|a b|}.{|escape file|}.A;
