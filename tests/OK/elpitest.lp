require open tests.OK.logic
require open tests.OK.bool
require open tests.OK.nat

elpi "tests/OK/elpitest.elpi" "main"
  (Πx y, P (eq ?T[x;y] x y) → P (eq ?T[x;y] y x))