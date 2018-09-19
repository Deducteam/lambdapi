/// Implementation of vectors
/// =========================
///
/// This module provides:
///  - a definition of vectors (lists of a given length),
///  - the usual **append** function for concatenation.

symbol const A : TYPE

symbol const Nat : TYPE

symbol const zero : Nat
symbol const succ : Nat ⇒ Nat

symbol plus : Nat ⇒ Nat ⇒ Nat
rule plus zero      &m → &m
rule plus (succ &n) &m → succ (plus &n &m)

symbol const Vec : Nat ⇒ TYPE
symbol const nil : Vec zero
symbol const cns : ∀ (n:Nat), A ⇒ Vec n ⇒ Vec (succ n)

symbol append : ∀ (n:Nat) (m:Nat), Vec n ⇒ Vec m ⇒ Vec (plus n m)
rule append _  _ nil             &l2 → &l2
rule append _ &m (cns &n &e &l1) &l2 →
  cns (plus &n &m) &e (append &n &m &l1 &l2)

// FIXME add more functions.

//theorem add_comm : ∀ (m:Nat) (n:Nat), eq Nat (add m n) (add n m)
//proof
//  intro m n
//abort
