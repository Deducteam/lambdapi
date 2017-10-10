def mult : examples::plus::nat ⇒ examples::plus::nat ⇒ examples::plus::nat.
[m]   mult examples::plus::Z     m → examples::plus::Z.
[m n] mult (examples::plus::S n) m → examples::plus::plus m (mult n m).
