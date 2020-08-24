symbol A:TYPE
symbol a:A
symbol f:(A→A)→A
rule f (λx,$M) ↪ a
// Error: Missing square brackets under binder.
