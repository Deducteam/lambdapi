// shallow embedding of natural deduction proofs

require open Logic.Zenon.FOL Logic.Zenon.ND Logic.Zenon.ND_eps;

rule ϵ ⊥ ↪  Π r, ϵ r;
rule ϵ ⊤ ↪  Π r, ϵ r → ϵ r;
rule ϵ ($p ∨ $q) ↪  Π r, ϵ (($p ⇒ r) ⇒ ($q ⇒ r) ⇒ r);
rule ϵ ($t = $u) ↪  Π r, ϵ (r $t ⇒ r $u);
rule ϵ ($p ∧ $q) ↪  Π r, ϵ (($p ⇒ $q ⇒ r) ⇒ r);
rule ϵ (∃ $p) ↪  Π r, ϵ ((∀ (λ x, $p x ⇒ r)) ⇒ r);

rule ⊤I ↪ λ p πp, πp;

rule ⊥E ↪ λ π⊥ p, π⊥ p;

rule @∧I ↪ λ p q πp πq r πp⇒q⇒r, πp⇒q⇒r πp πq;
rule @∧El ↪ λ p q πp∧q, πp∧q p (λ x _, x);
rule @∧Er ↪ λ p q πp∧q, πp∧q q (λ _ x, x);

rule @∨Il ↪ λ p q πp r πp⇒r _, πp⇒r πp;
rule @∨Ir ↪ λ p q πq r _ πq⇒r, πq⇒r πq;
rule @∨E ↪ λ p q π, π;

rule =I ↪ λ t, λ r, λ π, π;
rule @=E ↪ λ t u πt=u p πpt, πt=u p πpt;

rule @∃I ↪ λ p t πpt r h, h t πpt;
rule @∃E ↪ λ p π∃p, π∃p;
