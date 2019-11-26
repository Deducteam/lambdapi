// natural numbers
constant symbol N : TYPE
constant symbol z : N
constant symbol s : N ⇒ N

// two parameters function
constant symbol f : N ⇒ N ⇒ N

// without context without inference
assert λn:N, s n ≡ λn:N, s n
assert λn m:N, f n m ≡ λ(n m:N), f n m
assert λn:N, s n : ∀n:N, N // N → N
assert λn m:N, f n m : ∀n m, N // N → N → N

// without context with inference
assert λn, s n ≡ λn, s n
assert λn m, f n m ≡ λn m, f n m
assert λn, s n : ∀n, N // N → N
assert λn m, f n m : ∀n m, N // N → N -> N

// with context without inference
assert {(n:N)} s n ≡ s n
assert {(n m:N)} f n m ≡ f n m
assert {(n:N)} s n : N
assert {(n m:N)} f n m : N

// with context with inference
// assert {n} s n ≡  s n
// assert {n} s n : N
// assert {n m} f n m ≡ f n m
// assert {n m} f n m : N