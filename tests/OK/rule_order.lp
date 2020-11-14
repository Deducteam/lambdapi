symbol E: TYPE;
symbol e: E;
symbol ListE: TYPE;
symbol nil: ListE;
symbol cons: E → ListE → ListE;

symbol Bool: TYPE;
symbol true: Bool;
symbol false: Bool;

sequential symbol mem: E → ListE → Bool;
rule mem $e (cons $e _) ↪ true;
rule mem $e (cons _ $l) ↪ mem $e $l;
rule mem _ nil ↪ false;

symbol mem2: E → ListE → Bool;
rule mem2 $e (cons $e _) ↪ true;
rule mem2 $e (cons _ $l) ↪ mem $e $l;
rule mem2 _ nil ↪ false;

assert ⊢ mem e (cons e nil) ≡ true;
assert ⊢ mem2 e (cons e nil) ≡ false;
