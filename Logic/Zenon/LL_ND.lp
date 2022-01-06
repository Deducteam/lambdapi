// translation of Zenon LL proofs into natural deduction proofs

require open Logic.Zenon.FOL Logic.Zenon.LL Logic.Zenon.ND Logic.Zenon.ND_eps
             Logic.Zenon.ND_eps_full Logic.Zenon.ND_eps_aux;

rule R⊥ ↪ λ x : ϵ ⊥, x;

rule R¬⊤ ↪ λ h : ϵ (¬ ⊤), h ⊤I;

rule Rax ↪ λ p h π¬p, π¬p h;

rule R≠ ↪ λ t h1, h1 (=I t);

rule R= ↪ λ t u h1 h2, h2 (=E t u h1 (λ x, x = t) (=I t));

rule Rcut ↪ λ p h1 h2, h2 h1;

rule R¬¬ ↪ λ p h1 h2, h2 h1;

rule R∧ ↪ λ p q h1 h2, h1 (@∧El p q h2) (@∧Er p q h2);

rule R∨ ↪ λ p q h1 h2 h3, @∨E p q h3 ⊥ h1 h2;

rule R⇒ ↪ λ p q h1 h2 h3, h1 (Lcontraposition p q h3 h2);

rule R⇔ ↪ λ p q h1 h2 h3, L⇔4 p q (@∧Er (p ⇒ q) (q ⇒ p) h3)
                     h2 (@∧El (p ⇒ q) (q ⇒ p) h3) h1
                     (L⇔2 p q (@∧Er (p ⇒ q) (q ⇒ p) h3) h2);

rule R¬∧ ↪ λ p q h1 h2 h3,
  h1 (λ h5, h2 (λ h6, h3 (@∧I p q h5 h6))); 

rule R¬∨ ↪ λ p q h1 h2, h1 (L¬∨3 p q h2) (L¬∨4 p q h2); 

rule R¬⇒ ↪ λ p q h1 h2,
  h2 (λ h3 : ϵ p, ⊥E (h1 h3 (λ h4, h2 (λ _, h4))) q); 

rule R¬⇔ ↪ λ p q h1 h2 h3,
  (λ hnp, h3 (@∧I (p ⇒ q) (q ⇒ p) (λ hP : ϵ p, ⊥E (hnp hP) q) 
                (λ hQ : ϵ q, ⊥E (h1 hnp hQ) p)))
  (L¬⇔1 p q h2 h3);

rule R∃ ↪ λ p h1 h2, @∃E p h2 ⊥ h1;

rule R∀ ↪ λ p t h1 h2, h1 (h2 t); 

rule R¬∃ ↪ λ p t h1 h2, h1 (λ h4 : ϵ (p t), h2 (@∃I p t h4)); 

rule R¬∀ ↪ λ p h1 h2, h2 (λ t, @nnpp (p t) (h1 t));

rule Rσ ↪ λ p t u h1 h2 h3,
  h1 (λ h4, h2 (@=E t u h4 p h3));
