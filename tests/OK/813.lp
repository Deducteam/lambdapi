constant symbol Set : TYPE;
injective symbol El : Set → TYPE;
sequential symbol η (A : Set) : El A → El A;
rule η _ (η $A $x) ↪ η $A $x;

constant symbol Σ (A : Set) (B : El A → Set) : Set;
//constant symbol TypeΣ (A : Set) (B : El A → Set) : TYPE;
//rule El (Σ $A $B) ↪ TypeΣ $A (λ x, $B (η $A x));

constant symbol intro-Σ (A : Set) (B : El A → Set) (a : El A) (b : El (B (η A a))) : El (Σ A (λ x, B (η A x)));
symbol fst (A : Set) (B : El A → Set) (p : El (Σ A (λ x, B (η A x)))) : El A;
symbol snd (A : Set) (B : El A → Set) (p : El (Σ A (λ x, B (η A x)))) : El (B (η A (fst A (λ x, B (η A x)) p)));

//rule η (Σ $A $B) $p ↪ intro-Σ $A (λ x, $B (η $A x)) (η $A (fst $A (λ x, $B (η $A x)) $p)) (η ($B (η $A (fst $A (λ x, $B (η $A x)) $p))) (snd $A (λ x, $B (η $A x)) $p));

rule fst _ _ (intro-Σ $A _ $a _) ↪ η $A $a;

rule snd _ _ (intro-Σ $A $B $a $b) ↪ η ($B (η $A $a)) $b;
