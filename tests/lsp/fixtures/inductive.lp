constant symbol Bool : TYPE;

inductive Tree : TYPE ≔
| leaf : Tree
| node : Tree → Tree → Tree;

symbol height : Tree → Bool;
symbol mirror : Tree → Tree ≔ λ t, t;
