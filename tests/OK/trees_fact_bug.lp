symbol const Nat : TYPE
symbol const Z : Nat
symbol const S : Nat ⇒ Nat

set builtin "0" ≔ Z
set builtin "+1" ≔ S

symbol plus : Nat ⇒ Nat ⇒ Nat
rule plus Z      &x → &x
 and plus (S &x) &y → plus &x (S &y)

symbol mult : Nat ⇒ Nat ⇒ Nat
rule mult Z _       → Z
 and mult (S &x) &y → plus &y (mult &x &y)

symbol fact : Nat ⇒ Nat
rule fact Z → S Z
 and fact (S &x) → mult (S &x) (fact &x)


definition zero : Nat ≔ Z
definition one : Nat ≔ S Z
definition two : Nat ≔ S (S Z)
definition three : Nat ≔ S (S (S Z))
definition four : Nat ≔ S (S (S (S Z)))
definition five : Nat ≔ S (S (S (S (S Z))))
definition six : Nat ≔ (S (S (S (S (S (S Z))))))
definition seven : Nat ≔ (S (S (S (S (S (S (S Z)))))))
definition eight : Nat ≔ (S (S (S (S (S (S (S (S Z))))))))

compute mult seven (mult seven (mult seven (mult seven (mult seven seven))))

//compute zero
//compute one
//compute two
//compute three
//compute four
//compute five
//compute six
//compute seven

// compute (fact zero)
// compute mult (S Z) (S Z)
// compute (fact (S Z))

// compute (plus (fact 3) (fact 2))
// compute (plus (fact 2) (fact 3))

// compute (plus (fact 5) (fact 4))
// compute (plus (fact seven) (fact six))
// compute (plus (fact seven) (fact eight))
// compute (plus (fact eight) (fact seven))

// assert (plus (fact 5) (fact 4)) ≡ (plus (fact 4) (fact 5))
// assert (plus (fact seven) (fact six)) ≡ (plus (fact six) (fact seven))
// assert (plus (fact seven) (fact eight)) ≡ (plus (fact eight) (fact seven))
