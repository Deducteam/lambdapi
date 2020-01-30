require open std.bool

// Data type of binary natural numbers.

constant symbol N : TYPE

constant symbol zero        : N
constant symbol times2plus0 : N ⇒ N
constant symbol times2plus1 : N ⇒ N

// Successor function.

symbol succ : N ⇒ N

rule succ zero             → times2plus1 zero
 and succ (times2plus0 &n) → times2plus1 &n
 and succ (times2plus1 &n) → times2plus0 (succ &n)

// Enabling built-in natural number literal, and example.

set builtin "0"  ≔ zero
set builtin "+1" ≔ succ

definition forty_two ≔ 42

// Addition function.

symbol add : N ⇒ N ⇒ N
set infix left 6 "+" ≔ add

rule zero           + &m             → &m
 and &n             + zero           → &n
 and times2plus0 &n + times2plus0 &m → times2plus0 (&n + &m)
 and times2plus0 &n + times2plus1 &m → times2plus1 (&n + &m)
 and times2plus1 &n + times2plus0 &m → times2plus1 (&n + &m)
 and times2plus1 &n + times2plus1 &m → times2plus0 (succ (&n + &m))

// Multiplication function.

symbol mul : N ⇒ N ⇒ N
set infix left 7 "×" ≔ mul

definition times4 : N ⇒ N ≔ λ n, times2plus0 (times2plus0 n)

rule zero           × _              → zero
 and _              × zero           → zero
 and times2plus0 &n × times2plus0 &m → &n × times4 (&n × &m)
 and times2plus0 &n × times2plus1 &m → &n × times4 (&n × &m) + times2plus0 &n
 and times2plus1 &n × times2plus0 &m → &n × times4 (&n × &m) + times2plus0 &m
 and times2plus1 &n × times2plus1 &m → times4 (&n × &m) + times2plus1(&n + &m)

definition double n ≔ times2plus0 n
