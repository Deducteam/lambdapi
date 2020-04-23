symbol T: TYPE
symbol C: T → T
symbol D: T → T
symbol a: T

// A hint is sound if, considering P ≡ Q ↪ x1 ≡ H1, ..., xn ≡ Hn,
// P[x1 ≔ H1, ..., xn ≔ Hn] ≡ Q[x1 ≔ H1, ..., xn ≔ Hn]
// where ≡ stands for convertibility here.
hint C $x ≡ D $y ↪ $x ≡ D a, $y ≡ C a
// C (D a) is not convertible with D (C a), the rule is not valid.
