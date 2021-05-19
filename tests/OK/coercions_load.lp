// Verify that coercions are loaded with module
require open tests.OK.coercions;

assert ⊢ nat → Set ≡ El nat → Set;
