constant symbol A : TYPE;

constant symbol Nat : TYPE;
constant symbol zero : Nat;
constant symbol succ : Nat → Nat;

symbol plus : Nat → Nat → Nat;
rule plus zero      $m ↪ $m;
rule plus (succ $n) $m ↪ succ (plus $n $m);

constant symbol Vec : Nat → TYPE;
constant symbol nil : Vec zero;
constant symbol cns : Π (n:Nat), A → Vec n → Vec (succ n);

symbol append : Π (n:Nat) (m:Nat), Vec n → Vec m → Vec (plus n m);
rule append _  _ nil             $l2 ↪ $l2;
rule append _ $m (cns $n $e $l1) $l2 ↪
  cns (plus $n $m) $e (append $n $m $l1 $l2);
