/* Representation of the calculus of constructions. */

require open Logic.PTS.Main;

constant symbol s : Set;
constant symbol a : F s → F s → Set;
constant symbol r : F s → F s → F s → Set;

// sorts
constant symbol * : F s;
constant symbol □ : F s;

// axioms
constant symbol α₁ : F (a * □);

// rules
constant symbol ρ₁ : F (r * * *);
constant symbol ρ₂ : F (r □ * *);
constant symbol ρ₃ : F (r * □ □);
constant symbol ρ₄ : F (r □ □ □);
