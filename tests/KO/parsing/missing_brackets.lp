symbol A:TYPE;
symbol a:A;
symbol f:(A → A) → A;
rule f (λ x, $M) ↪ a;
// Error: Missing square brackets under binder.
