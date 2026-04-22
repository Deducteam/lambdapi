constant symbol Bool : TYPE;

inductive Tree : TYPE ≔
| leaf : Tree
| node : Tree → Tree → Tree;

symbol height : Tree → Bool;
