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
symbol const nil : Listn zero
symbol const cns : ∀ (n:Nat), A ⇒ Listn n ⇒ Listn (succ n)

symbol append : ∀ (n:Nat) (m:Nat), Listn n ⇒ Listn m ⇒ Listn (plus n m)
rule append _  _  nil             &l2 → &l2
rule append &n &m (cons _ &a &l1) &l2 →
  cons (plus &n &m) &a (append &n &m &l1 &l2)

// FIXME add more functions.

theorem add_comm : ∀ (m:Nat) (n:Nat), eq Nat (add m n) (add n m)
proof
  intro m n;
abort
