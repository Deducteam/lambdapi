// semi-shallow embedding of natural deduction proofs

require open Logic.Zenon.FOL Logic.Zenon.ND;

rule ϵ ($p ⇒ $q) ↪ ϵ $p → ϵ $q;
rule ϵ (∀ $p) ↪ Π x, ϵ ($p x);

rule ⇒I ↪ λ p q π, π;
rule ⇒E ↪ λ p q π, π;

rule ∀I ↪ λ p π, π;
rule ∀E ↪ λ p x π, π x;
