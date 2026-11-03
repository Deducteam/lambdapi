// unary natural numbers

/*
following https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnat.v

Documentation of ssrnat.v
-------------------------

The following operations and notations are provided:

successor and predecessor
     n +1 and n ∸1

basic arithmetic
  m + n, m - n, m * n
Important: m - n denotes TRUNCATED subtraction: m - n = 0 if m <= n.

exponentiation, factorial
     m ^ n, n !
     m ^ 1 is convertible to m, and m ^ 2 to m * m

comparison
   m <= n, m < n, m >= n, m > n, m == n, m <= n <= p, etc.,
comparisons are BOOLEAN operators.
  Most compatibility lemmas are stated as boolean equalities; this keeps
the size of the library down. All the inequalities refer to the same
constant "leq"; in particular m < n is identical to m.+1 <= n.

maximum and minimum
   maxn m n, minn m n
Note that maxn m n = m + (n - m), due to the truncating subtraction.

Not available
-------------

doubling, halving, and parity
   n.*2, n./2, odd n, uphalf n,  with uphalf n = n.+1./2
bool coerces to nat so we can write, e.g., n = odd n + n./2.*2.

iteration
          iter n f x0  == f ( .. (f x0))
          iteri n g x0 == g n.∸1 (g ... (g 0 x0))
      iterop n op x x0 == op x (... op x x) (n x's) or x0 if n = 0

conditionally strict inequality `leqif'
   m <= n ?= iff condition   ==   (m <= n) and ((m == n) = condition)
This is actually a pair of boolean equalities, so rewriting with an
`leqif' lemma can affect several kinds of comparison. The transitivity
lemma for leqif aggregates the conditions, allowing for arguments of
the form ``m <= n <= p <= m, so equality holds throughout''.

countable choice
  ex_minn : forall P : pred nat, (exists n, P n) -> nat
This returns the smallest n such that P n holds.
  ex_maxn : forall (P : pred nat) m,
     (exists n, P n) -> (forall n, P n -> n <= m) -> nat
This returns the largest n such that P n holds (given an explicit upper
bound).

Naming convention
-----------------

This file adds the following suffix conventions to those documented in
ssrbool.v and eqtype.v:
A (infix) -- conjunction, as in
   ltn_neqAle : (m < n) = (m != n) && (m <= n).
B -- subtraction, as in subBn : (m - n) - p = m - (n + p).
D -- addition, as in mulnDl : (m + n) * p = m * p + n * p.
M -- multiplication, as in expnMn : (m * n) ^ p = m ^ p * n ^ p.
p (prefix) -- positive, as in
   eqn_pmul2l : m > 0 -> (m * n1 == m * n2) = (n1 == n2).
P  -- greater than 1, as in
   ltn_Pmull : 1 < n -> 0 < m -> m < n * m.
S -- successor, as in addSn : n +1 + m = (n + m) +1.
V (infix) -- disjunction, as in
   leq_eqVlt : (m <= n) = (m == n) || (m < n).
X - exponentiation, as in lognX : logn p (m ^ n) = logn p m * n in
      file prime.v (the suffix is not used in this file).
Suffixes that abbreviate operations (D, B, M and X) are used to abbreviate
second-rank operations in equational lemma names that describe left-hand
sides (e.g., mulnDl); they are not used to abbreviate the main operation
of relational lemmas (e.g., leq_add2l).
For the asymmetrical exponentiation operator expn (m ^ n) a right suffix
indicates an operation on the exponent, e.g., expnM : m ^ (n1 * n2) = ...;
a trailing "n" is used to indicate the left operand, e.g.,
expnMn : (m1 * m2) ^ n = ... The operands of other operators are selected
using the l/r suffixes.
*/

require open tests.OK.Bool;

inductive ℕ : TYPE ≔
| _0 : ℕ
| +1 : ℕ → ℕ; notation +1 postfix 100;

// enable printing of natural numbers in decimal notation
builtin "nat_zero" ≔ _0;
builtin "nat_succ" ≔ +1;

// shortcuts
symbol _1 ≔ _0 +1;
symbol _2 ≔ _1 +1;
symbol _3 ≔ _2 +1;
symbol _4 ≔ _3 +1;
symbol _5 ≔ _4 +1;
symbol _6 ≔ _5 +1;
symbol _7 ≔ _6 +1;
symbol _8 ≔ _7 +1;
symbol _9 ≔ _8 +1;
symbol _10 ≔ _9 +1;

// Induction principle for nats from n to n+2
opaque symbol ind_ℕ2 (p : ℕ → Prop) : π (p _0) → π (p (_0 +1)) → (Π x0: ℕ, π (p x0) → π (p (x0 +1)) → π (p (x0 +1 +1))) → Π x: ℕ, π (p x) ≔
begin
  assume p h0 h1 ih x;
  have enough: π (p x ∧ p (x +1)) → π (p x) { assume h; refine ∧ₑ₁ h };
  refine enough _;
  remove enough;
  generalize x;
  induction
  { apply ∧ᵢ h0 h1 }
  {
    assume x ihx;
    apply ∧ᵢ
    { refine ∧ₑ₂ ihx }
    { apply ih x (∧ₑ₁ ihx) (∧ₑ₂ ihx) }
  }
end;

// Perform just a case analysis without induction hypothesis
opaque symbol case_ℕ (p : ℕ → Prop) : π (p _0) → (Π x: ℕ, π (p (x +1))) → Π x: ℕ, π (p x) ≔
begin
  assume p h1 h2;
  induction
  {refine h1}
  {assume x h3;apply h2}
end;

// set code for ℕ

constant symbol nat : Set;

rule τ nat ↪ ℕ;

// non confusion of constructors

symbol is0 : ℕ → 𝔹;

rule is0 _0 ↪ true
with is0 (_ +1) ↪ false;

opaque symbol s≠0 [n] : π (n +1 ≠ _0) ≔
begin
  assume n h; refine ind_eq h (λ n, istrue(is0 n)) ⊤ᵢ
end;

opaque symbol 0≠s [n] : π (_0 ≠ n +1) ≔
begin
  assume n h; apply @s≠0 n; symmetry; apply h
end;

opaque symbol casen n : π(n = _0 ∨ n ≠ _0) ≔
begin
  induction
  { apply ∨ᵢ₁; reflexivity }
  { assume n h; apply ∨ᵢ₂; refine s≠0 }
end;

// predecessor

symbol ∸1 : ℕ → ℕ; notation ∸1 postfix 100;

rule _0 ∸1 ↪ _0
with ($x +1) ∸1 ↪ $x;

opaque symbol +1_inj [x y] : π (x +1 = y +1) → π (x = y) ≔
begin
  assume x y h; apply feq (∸1) h
end;

// boolean equality on ℕ

symbol eqn : ℕ → ℕ → 𝔹;

rule eqn _0 _0 ↪ true
with eqn ($x +1) ($y +1) ↪ eqn $x $y
with eqn _0 (_ +1) ↪ false
with eqn (_ +1) _0 ↪ false;

opaque symbol eqn_correct x y : π(istrue(eqn x y)) → π(x = y) ≔
begin
  induction
  { induction { reflexivity } { assume x h i; apply ⊥ₑ i } }
  { assume x h; induction
    { assume i; apply ⊥ₑ i }
    { assume y i j; apply feq (+1); apply h _ j }
  }
end;

opaque symbol eqn_complete x y : π(x = y) → π(istrue(eqn x y)) ≔
begin
  induction
  { assume y i; rewrite left i; apply ⊤ᵢ }
  { simplify; assume x h; induction
    { assume i; apply s≠0 i }
    { assume y i j; simplify; refine h y _; apply +1_inj; refine j }
  }
end;

opaque symbol eqn_sym x y : π(eqn x y) → π(eqn y x) ≔
begin
  assume x y h; refine eqn_complete y x _;
  symmetry;
  refine eqn_correct x y _; refine h
end;

opaque symbol eqn_refl x : π(eqn x x) ≔
begin
  assume x; refine eqn_complete x x _; reflexivity
end;

// addition

symbol + : ℕ → ℕ → ℕ; notation + infix left 20;

rule _0 + $y ↪ $y
with $x +1 + $y ↪ ($x + $y) +1;

opaque symbol add0n x : π (_0 + x = x) ≔
begin reflexivity end;

opaque symbol addn0 x : π (x + _0 = x) ≔
begin
  induction
  { reflexivity }
  { assume x' h; simplify; rewrite h; reflexivity }
end;

opaque symbol addSn x y : π (x +1 + y = (x + y) +1) ≔
begin reflexivity end;

opaque symbol addnS x y : π (x + y +1 = (x + y) +1) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite h; reflexivity }
end;

opaque symbol suc=+1 x : π ((x +1) = (x + _1))≔
begin
  induction
    {reflexivity}
    {assume n h; rewrite h; rewrite left addSn; rewrite h; reflexivity;}
end;

opaque symbol add1n n : π ((_0 +1) + n = n +1) ≔
begin
  reflexivity;
end;

opaque symbol addn1 n : π (n + (_0 +1) = n +1) ≔
begin
  assume n; rewrite (addnS n _0); rewrite addn0;
  reflexivity;
end;

opaque symbol addSnnS m n : π (m +1 + n = m + n +1) ≔
begin
  assume m n; rewrite (addnS m n);
  rewrite addSn m n;
  reflexivity;
end;

opaque symbol addnC x y : π (x + y = y + x) ≔
begin
  induction
  { assume y; rewrite addn0; reflexivity }
  { assume x' h y; simplify; rewrite h;
  rewrite addnS (y) (x'); reflexivity }
end;

opaque symbol addnA x y z : π ((x + y) + z = x + (y + z)) ≔
begin
  induction
  { reflexivity }
  { assume x' h y z; simplify; rewrite h; reflexivity }
end;

opaque symbol addnCA m n p : π ((m + n) + p = (m + p) + n) ≔
begin
  assume m n p; symmetry; rewrite addnA; rewrite .[p + n] addnC;
  rewrite left addnA; reflexivity;
end;

opaque symbol addnAC m n p : π (m + (n + p) = n + (m + p)) ≔
begin
  assume m n p; symmetry; rewrite left addnA; rewrite .[n + m] addnC;
  rewrite addnA; reflexivity;
end;

opaque symbol addnCAC m n p : π (m + n + p = p + n + m) ≔
begin
  assume m n p; rewrite addnC; rewrite .[m + _] addnC; rewrite addnA;
  reflexivity;
end;

opaque symbol addnACl m n p : π (m + n + p = n + (p + m)) ≔
begin
  assume m n p; rewrite .[m + _] addnC; rewrite addnA; rewrite .[m + _] addnC;
  reflexivity;
end;

opaque symbol addnACA m n p q : π ((m + n) + (p + q) = (m + p) + (n + q)) ≔
begin
  assume m n p q; rewrite addnA; rewrite addnA; rewrite left .[p + (n + q)] addnA;
  rewrite .[p + n] addnC; rewrite .[(n + p) + q] addnA; reflexivity;
end;

opaque symbol addnI x y z : π (z + x = z + y) → π (x = y) ≔
begin
  assume x y; induction
  { assume h; apply h;}
  { assume z h i; apply h; apply +1_inj; apply i;}
end;

opaque symbol addIn x y z : π (x + z = y + z) → π (x = y) ≔
begin
  assume x y; induction
  { rewrite addn0 x; rewrite addn0 y; assume h; apply h;}
  { assume z h i; apply h; apply +1_inj;
  rewrite left addnS x z; rewrite left addnS y z; apply i;}
end;

opaque symbol addn_eq0 m n : π (m + n = _0 ⇔ m = _0 ∧ n = _0) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume m h; apply ∧ᵢ (eq_refl _0) h }
    { assume m h n i; apply ⊥ₑ (s≠0 i) }
  } {
    generalize m; induction
    { assume n h; apply ∧ₑ₂ h }
    { assume m h n i; apply ⊥ₑ (s≠0 (∧ₑ₁ i)) }
  }
end;

opaque symbol eqn_add2l p m n : π ((p + m = p + n) ⇔ (m = n)) ≔
begin
  assume p m n;
  apply ∧ᵢ {
    refine addnI m n p
  } {
    generalize p; induction
    { assume m n h; apply h }
    { assume z h m n i; simplify; rewrite h m n i; reflexivity }
  };
end;

opaque symbol eqn_add2r p m n : π ((m + p = n + p) ⇔ (m = n)) ≔
begin
  assume p m n; rewrite addnC m p; rewrite addnC n p; apply eqn_add2l p m n;
end;

opaque symbol 2*=0 n : π(n + n = _0) → π(n = _0) ≔
begin
  assume n h; apply ∧ₑ₁ (∧ₑ₁ (addn_eq0 n n) h)
end;

opaque symbol 2*_inj x y : π(x + x = y + y) → π(x = y) ≔
begin
  induction
  { assume y h; symmetry; apply 2*=0; symmetry; apply h }
  { assume x h; induction
    { assume i; apply ⊥ₑ (s≠0 i) }
    { assume y i j; apply feq (+1); apply h; apply +1_inj;
      rewrite left addnS x x; rewrite left addnS y y; apply +1_inj j }
}
end;

symbol even: ℕ → 𝔹;
rule even _0 ↪ true
with even (_0 +1) ↪ false
with even ($x +1 +1) ↪ even $x;

symbol odd (n: ℕ): 𝔹 ≔ not (even n);

opaque symbol evenS n : π (even (n +1) = not (even n)) ≔
begin
  induction
  { reflexivity }
  { assume n ih; simplify; rewrite ih; rewrite notK; reflexivity }
end;

opaque symbol oddS n : π (odd (n +1) = not (odd n)) ≔
begin
  assume n; simplify; rewrite evenS; reflexivity
end;

opaque symbol even_odd n : π (even n = not (odd n)) ≔
begin
  assume n; simplify; symmetry; apply notK
end;

opaque symbol even_addnn n : π (even (n + n)) ≔
begin
  induction
  { apply ⊤ᵢ }
  { assume n ih; rewrite addnS; apply ih }
end;

opaque symbol odd_addnnS n : π (odd ((n + n) +1)) ≔
begin
  assume n; rewrite evenS; rewrite notK; refine even_addnn n
end;

opaque symbol odd≠even m n : π (odd m) → π (even n) → π (m ≠ n) ≔
begin
  assume m n hm hn h;
  refine istrue_not hm (ind_eq h (λ z, istrue (even z)) hn)
end;

opaque symbol addnnS≠addnn p q : π ((p + p) +1 ≠ q + q) ≔
begin
  assume p q;
  refine odd≠even ((p + p) +1) (q + q) (odd_addnnS p) (even_addnn q)
end;

// substraction

symbol - : ℕ → ℕ → ℕ; notation - infix left 20;

rule _0 - _ ↪ _0
with $x +1 - _0 ↪ $x +1
with $x +1 - $y +1 ↪ $x - $y;

opaque symbol sub0n n : π (_0 - n = _0) ≔
begin
  reflexivity;
end;

opaque symbol subn0 n : π (n - _0 = n) ≔
begin
  induction
    {reflexivity}
    {reflexivity}
end;

opaque symbol subnn x : π (x - x = _0) ≔
begin
  induction
  { reflexivity }
  { assume x h; simplify; apply h;}
end;

opaque symbol subSS m n : π (m +1 - (n +1) = m - n) ≔
begin
  reflexivity;
end;

opaque symbol subn1 n : π (n - (_0 +1) = n ∸1) ≔
begin
  induction
  { reflexivity }
  { assume n h; simplify; rewrite subn0; reflexivity;  }
end;

opaque symbol subnS x y : π (x - (y +1) = (x - y) ∸1) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { simplify; rewrite subn0; reflexivity }
    { assume y i; simplify; rewrite h; reflexivity }
    }
end;

opaque symbol subSnn n : π (n +1 - n = (_0 +1)) ≔
begin
  induction
  { reflexivity }
  { assume n h; simplify; apply h }
end;

opaque symbol predn_sub x y : π ((x - y) ∸1 = x ∸1 - y) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { simplify; rewrite subn0; reflexivity }
    { assume y i; simplify; symmetry; rewrite subnS; reflexivity }
}
end;

opaque symbol subnAC z x y : π ((x - y) - z = (x - z) - y) ≔
begin
  induction
  { assume x y; rewrite subn0; rewrite subn0; reflexivity }
  { assume z h; induction
    { reflexivity }
    { assume x i; induction
      { simplify; rewrite subn0; reflexivity}
      { assume y j; simplify; rewrite i; rewrite subnS; symmetry;
        rewrite subnS; rewrite predn_sub; reflexivity}
    }
  }
end;

opaque symbol addnK x y : π ((x + y) - y = x) ≔
begin
  induction
  { assume x; simplify; rewrite subnn; reflexivity }
  { assume x h; induction
    { rewrite addn0 (x +1); reflexivity }
    { simplify; assume y i; rewrite addnS x y; rewrite i; reflexivity }
  }
end;

opaque symbol subnDA x y z : π (x - (y + z) = (x - y) - z) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { rewrite addn0 (y +1); simplify; rewrite subn0; reflexivity }
      { assume z j; simplify; rewrite addnS y z; rewrite subnS; symmetry; rewrite subnS;
        rewrite h; reflexivity }
    }
  }
end;

opaque symbol subnDl z x y : π ((z + x) - (z + y) = x - y) ≔
begin
  induction
  { assume x y; simplify; reflexivity }
  { assume z h; induction
    { assume y; simplify; rewrite addn0 z; rewrite subnDA; rewrite subnn; reflexivity }
    { assume x i; induction
      { rewrite addnC; rewrite addn0; rewrite addnK; reflexivity }
      { assume y j; rewrite addnC; rewrite subnDA; rewrite addnK; reflexivity }
    }
  }
end;

opaque symbol subnDr z x y : π ((x + z) - (y + z) = x - y) ≔
begin
  assume z x y; rewrite addnC; rewrite .[y + _] addnC; rewrite subnDl;
  reflexivity;
end;

opaque symbol subSKn m n : π ((m +1 - n) ∸1 = m - n) ≔
begin
  assume m n; rewrite left subnS; reflexivity;
end;

// multiplication

symbol * : ℕ → ℕ → ℕ; notation * infix left 30; // \times

assert x y z ⊢ x + y * z ≡ x + (y * z);

rule _0 * _  ↪ _0
with ($x +1) * $y ↪ $y + $x * $y;

opaque symbol mul0n x : π (_0 * x = _0) ≔
begin reflexivity end;

opaque symbol muln0 x : π (x * _0 = _0) ≔
begin
  induction { reflexivity } { assume x' h; apply h }
end;

opaque symbol mul1n n : π ((_0 +1) * n = n) ≔
begin
  assume n; simplify; rewrite addn0 n; reflexivity;
end;

opaque symbol muln1 n : π (n * (_0 +1) = n) ≔
begin
  induction
  { reflexivity }
  { assume n h; simplify; rewrite h; reflexivity }
end;

opaque symbol mulSn m n : π ((m +1) * n = n + m * n) ≔
begin
  reflexivity;
end;

opaque symbol mulSnr m n : π ((m +1) * n = m * n + n) ≔
begin
  assume m n; rewrite addnC; reflexivity;
end;

opaque symbol mulnS x y : π (x * (y +1) = x + x * y) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite h; rewrite addnAC; reflexivity }
end;

opaque symbol muln2 n: π (n * _2 = n + n) ≔
begin
assume n; simplify; rewrite mulnS; rewrite muln1; reflexivity
end;

opaque symbol mulnSr x y : π (x * (y +1) = x * y + x) ≔
begin
  induction
  { reflexivity }
  { assume x' h y; simplify; rewrite mulnS; rewrite .[x' + _] addnC; rewrite addnA;
    rewrite addnS (x' * y) x'; rewrite addnS y ((x' * y) + x'); reflexivity }
end;

opaque symbol mulnC x y : π (x * y = y * x) ≔
begin
  induction
  { assume n; rewrite muln0; reflexivity }
  { assume x' h y; simplify; rewrite mulnS; rewrite h; reflexivity }
end;

opaque symbol mulnDl x y z : π ((x + y) * z = x * z + y * z) ≔
begin
  induction
  { reflexivity }
  { assume x' h y z; simplify; rewrite h; rewrite addnA; reflexivity }
end;

opaque symbol mulnDr x y z : π (z * (x + y) = z * x + z * y) ≔
begin
  assume x y z; rewrite mulnC; rewrite mulnDl; rewrite mulnC;
  rewrite .[y * _] mulnC; reflexivity
end;

opaque symbol mulnBr x y z : π (x * (y - z) = x * y - x * z) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { assume n; rewrite muln0; simplify; rewrite muln0; reflexivity }
    { assume y i; induction
      { simplify; rewrite muln0; rewrite subn0; reflexivity}
      { assume z j; simplify; rewrite mulnS; rewrite mulnS;
        rewrite left addnAC; rewrite .[z + (x + _)] addnAC;
        rewrite subnDl; rewrite left mulSn; rewrite left mulSn;
        rewrite left mulSn; rewrite left i; reflexivity }
    }
  }
end;

opaque symbol mulnBl x y z : π ((x - y) * z = x * z - y * z) ≔
begin
  assume x y z; rewrite mulnC; rewrite .[x * z] mulnC; rewrite .[y * z] mulnC;
  rewrite left mulnBr; reflexivity;
end;

opaque symbol mulnA x y z : π ((x * y) * z = x * (y * z)) ≔
begin
  induction
  { reflexivity }
  { assume x' h y z; simplify; rewrite mulnDl; rewrite h; reflexivity }
end;

opaque symbol mulnCA x y z: π (x * (y * z) = y * (x * z)) ≔
begin
  assume x y z; rewrite left mulnA; rewrite .[x * y] mulnC; rewrite mulnA;
  reflexivity;
end;

opaque symbol mulnAC x y z: π ((x * y) * z = (x * z) * y) ≔
begin
  assume x y z; rewrite mulnA; rewrite .[y * z] mulnC; rewrite left mulnA;
  reflexivity;
end;

opaque symbol mulnACA x y z t: π ((x * y) * (z * t) = (x * z) * (y * t)) ≔
begin
  assume x y z t; rewrite mulnA; rewrite .[y * _] mulnCA; rewrite mulnA;
  reflexivity;
end;

opaque symbol muln_eq0 m n : π (m * n = _0 ⇔ m = _0 ∨ n = _0) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n h; apply ∨ᵢ₁ h }
    { assume m h n i;
      have t: π (n = _0 ∧ (m * n) = _0) { apply ∧ₑ₁ (addn_eq0 n (m * n)) i };
      have u: π (n = _0) { apply ∧ₑ₁ t };
      apply ∨ᵢ₂ u;
    }
  } {
    assume h;
    refine ∨ₑ h _ _ {
      assume i; rewrite i; reflexivity;
    } {
      assume i; rewrite i; rewrite muln0; reflexivity;
    };
  };
end;

// enable parsing of decimal notation

builtin "0" ≔ _0;
builtin "1" ≔ _1;
builtin "2" ≔ _2;
builtin "3" ≔ _3;
builtin "4" ≔ _4;
builtin "5" ≔ _5;
builtin "6" ≔ _6;
builtin "7" ≔ _7;
builtin "8" ≔ _8;
builtin "9" ≔ _9;
builtin "10" ≔ _10;
builtin "+" ≔ +;
builtin "*" ≔ *;

// Boolean ordering functions

symbol ≤ : ℕ → ℕ → 𝔹; notation ≤ infix left 10;

rule _0 ≤ _ ↪ true
with _ +1 ≤ _0 ↪ false
with $x +1 ≤ $y +1 ↪ $x ≤ $y;

symbol < : ℕ → ℕ → 𝔹; notation < infix 10;

rule $x < $y ↪ $x +1 ≤ $y;

symbol ≥ : ℕ → ℕ → 𝔹; notation ≥ infix 10;

rule $x ≥ $y ↪ $y ≤ $x;

symbol > : ℕ → ℕ → 𝔹; notation > infix 10;

rule $x > $y ↪ $y +1 ≤ $x;

opaque symbol ≤0 x : π (istrue (x ≤ _0)) → π (x = _0) ≔
begin
  induction
  { reflexivity;}
  { assume x h i; apply ⊥ₑ; apply i }
end;

opaque symbol ≤_refl x : π (istrue (x ≤ x)) ≔
begin
  induction
  { simplify; apply ⊤ᵢ;}
  { assume x h; simplify; apply h }
end;

opaque symbol eq_leq x y : π (x = y) → π (istrue (x ≤ y)) ≔
begin
  assume x y h; rewrite h; apply ≤_refl y;
end;

opaque symbol leq_trans [x y z] :
  π (istrue (x ≤ y)) → π (istrue (y ≤ z)) → π (istrue (x ≤ z)) ≔
begin
  induction
  { assume y z h i; apply h }
  { assume x h; induction
    { assume y i; apply ⊥ₑ i }
    { assume y i; induction
      { assume j k; apply k }
      { assume z j k l; apply h y z k l }
    }
  }
end;

opaque symbol eqn_leq x y : π (istrue (x ≤ y) ∧ istrue (y ≤ x) ⇔ (x = y)) ≔
begin
  assume x y; apply ∧ᵢ {
    generalize x; induction
    { assume y g;
      have i: π (istrue (y ≤ _0)) { apply ∧ₑ₂ g };
      symmetry; apply ≤0 y i;
    }
    {
      assume x h; induction
      { assume g;
        have i: π (istrue (x +1 ≤ _0)) { apply ∧ₑ₁ g };
        apply ≤0 (x +1) i;
      }
      { assume y i j; apply feq (+1); apply h y j;}
    }
  } {
    assume h;
    have t: π (istrue (x ≤ y)) { apply eq_leq _ _ h;};
    have u: π (istrue (y ≤ x)) { apply eq_leq y x _; symmetry; apply h;};
    apply ∧ᵢ t u;
  };
end;

opaque symbol leqsnn n: π (istrue (n +1 ≤ n)) → π ⊥ ≔
begin
  induction
  { assume h; apply h }
  { assume n h i; apply h; apply i;}
end;

opaque symbol letnS m n : π (istrue (m < n +1)) → π (istrue (m ≤ n)) ≔
begin
  assume m n h; apply h;
end;

opaque symbol ltn0 n : π (istrue (n < _0)) → π ⊥ ≔
begin
  assume n h; apply h;
end;

opaque symbol ltnn n : π (istrue (n < n)) → π ⊥ ≔
begin
  assume n h; apply leqsnn n; apply h;
end;

opaque symbol ltnSn n : π (istrue (n < n +1)) ≔
begin
  assume n; simplify; apply ≤_refl n;
end;

opaque symbol leq0n n : π (istrue (_0 ≤ n)) ≔
begin
  induction
  { apply ≤_refl _0;}
  { assume n h; simplify; apply h }
end;

opaque symbol ltn0Sn n : π (istrue (_0 < n +1)) ≔
begin
  assume n; apply leq0n n;
end;

opaque symbol leqnSn n : π (istrue (n ≤ n +1)) ≔
begin
  induction
  { apply leq0n (_0 +1) }
  { assume n h; simplify; apply h }
end;

opaque symbol leq_pred n : π (istrue (n ∸1 ≤ n)) ≔
begin
  induction
  { apply ⊤ᵢ;}
  { assume n h; simplify; apply leqnSn n;}
end;

opaque symbol ltnW m n : π (istrue (m < n)) → π (istrue (m ≤ n)) ≔
begin
  induction
  { assume m h; apply ⊤ᵢ;}
  { assume m h; induction
    { assume i; apply i;}
    { assume n i j; apply h n; apply j;}
  }
end;

opaque symbol leqW m n : π (istrue (m ≤ n)) → π (istrue (m ≤ n +1)) ≔
begin
  assume m n h; apply ltnW m (n +1); simplify; apply h;
end;

opaque symbol ltn_trans x y z : π (istrue (x < y)) → π (istrue (y < z)) → π (istrue (x < z)) ≔
begin
  assume x y z h i;
  have v:π (istrue (x +1 ≤ y +1)) { apply leqW (x +1) y h };
  apply @leq_trans (x +1) (y +1) z v i;
end;

opaque symbol <_asym x y : π (istrue (x < y)) → π (¬ (istrue (y < x))) ≔
begin
  assume x y h i;
  have t:π (istrue (y ≤ y +1)) { apply leqnSn y };
  have u:π (istrue (x +1 ≤ y +1)) { apply @leq_trans (x +1) y (y +1) h t };
  have v:π (istrue (x +1 ≤ x)) { apply @leq_trans (x +1) (y +1) x u i };
  apply leqsnn x; apply v;
end;

opaque symbol anti_ltn x y : π(istrue (x < y)) → π(istrue (y < x)) → π(x = y) ≔
begin
  assume x y h i;
  have c:π (istrue (x ≤ x +1)) { apply leqnSn x };
  have d:π (istrue (y ≤ y +1)) { apply leqnSn y };
  have e:π (istrue (x ≤ y)) { apply @leq_trans x (x +1) y c h };
  have f:π (istrue (y ≤ x)) { apply @leq_trans y (y +1) x d i };
  have g:π (istrue (x ≤ y) ∧ istrue (y ≤ x)) { apply ∧ᵢ e f };
  apply ∧ₑ₁ (eqn_leq x y) g;
end;

opaque symbol leq_total x y : π (istrue (x ≤ y) ∨ istrue (y ≤ x)) ≔
begin
  induction
  { assume y; simplify; apply ∨ᵢ₁; apply ⊤ᵢ }
  { assume x h; induction
    { simplify; apply ∨ᵢ₂; apply ⊤ᵢ }
    { assume y i; simplify; apply h y }
  }
end;

opaque symbol lt0n n : π (istrue (n > _0) ⇔ (n ≠ _0)) ≔
begin
  assume n; apply ∧ᵢ {
    generalize n; induction
    { assume h i; apply h }
    { assume n h i j; apply s≠0 j;}
  } {
    generalize n; induction
    { assume h; apply h (eq_refl _0) }
    { assume n h i; apply ⊤ᵢ }
  };
end;

opaque symbol leq_eqVlt m n : π (istrue (m ≤ n) ⇔ (m = n) ∨ istrue (m < n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { induction
      { assume h; apply ∨ᵢ₁ (eq_refl _0) }
      { assume n h i; apply ∨ᵢ₂ ⊤ᵢ }
    }
    { assume m h; induction
      { assume i; apply ∨ᵢ₂ i }
      { assume n i j; apply ∨ₑ (h n j)
        { assume e; apply ∨ᵢ₁; rewrite e; reflexivity }
        { assume e; apply ∨ᵢ₂; apply e }
      }
    }
  } {
    assume h; apply ∨ₑ h {
      assume i; apply eq_leq m n i
    } {
      assume i; apply ltnW m n i
    }
  }
end;

opaque symbol leq_add0 m n :
  π (istrue (_0 ≤ m)) → π (istrue (_0 ≤ n)) → π (istrue (_0 ≤ m + n)) ≔
begin
  assume m n h i; apply leq0n (m + n);
end;

opaque symbol leq_add2l p m n : π (istrue (p + m ≤ p + n) ⇔ istrue (m ≤ n)) ≔
begin
  assume p m n; apply ∧ᵢ {
    generalize p; induction
    { assume m n h; apply h }
    { assume p h m n i; apply h m n i }
  } {
    generalize p; induction
    { assume m n h; apply h }
    { assume p h m n i; apply h m n i }
  };
end;

opaque symbol ltn_add2l p m n : π (istrue (p + m < p + n) ⇔ istrue (m < n)) ≔
begin
  assume p m n; simplify; rewrite left addnS; refine leq_add2l p (m +1) n;
end;

opaque symbol leq_add2r p m n : π (istrue (m + p ≤ n + p) ⇔ istrue (m ≤ n)) ≔
begin
  assume p m n; rewrite addnC m p; rewrite addnC n p; refine leq_add2l p m n;
end;

opaque symbol ltn_add2r p m n : π (istrue (m + p < n + p) ⇔ istrue (m < n)) ≔
begin
  assume p m n; rewrite addnC m p; rewrite addnC n p; refine ltn_add2l p m n;
end;

opaque symbol leq_addl m n : π (istrue (n ≤ m + n)) ≔
begin
  assume m; induction
  { apply ⊤ᵢ }
  { assume n h; rewrite addnS m n; apply h }
end;

opaque symbol leq_addr m n : π (istrue (n ≤ n + m)) ≔
begin
  assume m n; rewrite addnC n m; apply leq_addl m n;
end;

opaque symbol leq_subr m n : π (istrue (n - m ≤ n)) ≔
begin
  induction
  { assume n; rewrite subn0; apply ≤_refl n }
  { assume m h; induction
    { apply ⊤ᵢ }
    { assume n i; simplify;
      have t: π (istrue (n ≤ n +1)) { apply leqnSn n };
      apply @leq_trans (n - m) n (n +1) (h n) t;
    }
  }
end;

opaque symbol subn_eq0 m n : π ((m - n = _0) ⇔ istrue (m ≤ n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n h; apply ⊤ᵢ }
    { assume m h; induction
      { assume i; apply s≠0 i }
      { assume n i j; apply h n j }
    }
  } {
    generalize m; induction
    { assume n h; apply eq_refl _0 }
    { assume m h; induction
      { assume i; apply ⊥ₑ i }
      { assume n i j; apply h n j }
    }
  };
end;

opaque symbol ltn_addl m n p : π (istrue (m < n)) → π (istrue (m < p + n)) ≔
begin
  assume m n; induction
  { assume h; apply h }
  { assume p h i; refine @leq_trans m (m +1) (p + n) (leqnSn m) (h i) }
end;

opaque symbol ltn_addr m n p : π (istrue (m < n)) → π (istrue (m < n + p)) ≔
begin
  assume m n p h; rewrite addnC n p; apply ltn_addl m n p; apply h;
end;

opaque symbol addn_gt0 m n :
  π (istrue (_0 < m + n) ⇔ istrue (_0 < m) ∨ istrue (_0 < n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n i; apply ∨ᵢ₂ i }
    { assume m h n i; apply ∨ᵢ₁; apply ltn0Sn m }
  } {
    assume h; apply ∨ₑ h {
      assume i; apply ltn_addr _0 m n i;
    } {
      assume i; apply ltn_addl _0 n m i;
    };
  };
end;

opaque symbol subn_gt0 m n : π (istrue (_0 < n - m) ⇔ istrue (m < n)) ≔
begin
  assume m n; apply ∧ᵢ {
    generalize m; induction
    { assume n; rewrite subn0; assume h; apply h }
    { assume m h; induction
      { assume i; apply i }
      { assume n i; rewrite subSS; assume j;
        have t: π (istrue (m < n)) { apply h n j };
        simplify; apply t;
      }
    }
  } {
    generalize m; induction
    { assume n h; rewrite subn0; apply h }
    { assume m h; induction
      { assume i; apply i }
      { assume n i j; rewrite subSS; apply h n; simplify; apply j;
      }
    }
  };
end;

opaque symbol leq_add m1 m2 n1 n2 :
  π (istrue (m1 ≤ n1)) → π (istrue (m2 ≤ n2)) → π (istrue (m1 + m2 ≤ n1 + n2)) ≔
begin
  assume m1 m2 n1 n2 h i;
  have a: π (istrue (m1 + m2 ≤ m1 + n2)) { apply ∧ₑ₂ (leq_add2l m1 m2 n2) i };
  have b: π (istrue (m1 + n2 ≤ n1 + n2)) { refine ∧ₑ₂ (leq_add2r n2 m1 n1) h };
  refine @leq_trans (m1 + m2) (m1 + n2) (n1 + n2) a b;
end;

opaque symbol leq_subLR m n p : π (istrue (m - n ≤ p) ⇔ istrue (m ≤ n + p)) ≔
begin
  assume m n p; apply ∧ᵢ
  { assume h;
    have t: π (((m - (n + p)) = _0)) → π (istrue (m ≤ (n + p)))
      { apply ∧ₑ₁ (subn_eq0 m (n + p)) };
    apply t; rewrite subnDA; apply ∧ₑ₂ (subn_eq0 (m - n) p) h;
  }
  { assume h;
    have t: π (((m - n) - p) = _0) → π (istrue ((m - n) ≤ p))
      { apply ∧ₑ₁ (subn_eq0 (m - n) p) };
    apply t; rewrite left subnDA; apply ∧ₑ₂ (subn_eq0 m (n + p)) h;
  };
end;

opaque symbol subnKC m n : π (istrue (m ≤ n)) → π (m + (n - m) = n) ≔
begin
  induction
  { assume n h; rewrite subn0; apply eq_refl n }
  { assume m h; induction
    { assume i; apply ⊥ₑ i }
    { assume n i j; apply feq (+1); apply h; apply j }
  }
end;

opaque symbol addnBn m n : π (m + (n - m) = m - n + n) ≔
begin
  induction
  { assume n; rewrite subn0; apply eq_refl n }
  { assume m h; induction
    { reflexivity }
    { assume n i; simplify; rewrite addnS (m - n) n; apply feq (+1); apply h n }
  }
end;

opaque symbol subnK m n : π (istrue (m ≤ n)) → π ((n - m) + m = n) ≔
begin
  assume m n h; rewrite addnC; apply subnKC m n h;
end;

opaque symbol subSn n p : π (istrue (p ≤ n)) → π (n +1 - p = (n - p) +1) ≔
begin
  induction
  { assume p h; simplify;
    have t: π (p = _0) { apply ≤0 p h };
    rewrite t; reflexivity;
  } {
    assume n h; induction
    { reflexivity }
    { assume p i j; apply h p j }
  }
end;

opaque symbol addnBA m n p : π (istrue (p ≤ n))  → π (m + (n - p) = m + n - p) ≔
begin
  induction
  { reflexivity }
  { assume m h n p i; simplify; rewrite left addnS m (n - p);
    rewrite left addnS m n; rewrite left h (n +1) p (leqW p n i);
    rewrite subSn n p i; reflexivity;
  }
end;

opaque symbol addnBAC m n p : π (istrue (n ≤ m)) → π (m - n + p = m + p - n) ≔
begin
  assume m n p h;
  rewrite addnC; rewrite addnBA p m n h; rewrite addnC; reflexivity;
end;

opaque symbol leq_sub2r m n p :
  π (istrue (m ≤ n)) → π (istrue (m - p ≤ n - p)) ≔
begin
  assume m n p h; apply ∧ₑ₂ (leq_subLR m p (n - p)) _;
  apply ∨ₑ (leq_total p n) {
    assume i; rewrite subnKC p n i; apply h;
  } {
    assume i;
    have t: π(n - p = _0) { apply ∧ₑ₂ (subn_eq0 n p) i };
    rewrite t; rewrite addn0 p; apply @leq_trans m n p h i;
  };
end;

opaque symbol leq_sub2l m n p :
  π (istrue (m ≤ n)) → π (istrue (p - n ≤ p - m)) ≔
begin
  assume m n p h; apply ∧ₑ₂ (leq_subLR p n (p - m)) _;
  apply ∨ₑ (leq_total p m) {
    assume i;
    have t:π (p - m = _0) { apply (∧ₑ₂ (subn_eq0 p m) i) };
    rewrite t; rewrite addn0 n; apply @leq_trans p m n i h;
  } {
    assume i; apply ∧ₑ₁ (leq_add2r m p (n + (p - m))) _;
    rewrite addnA; rewrite subnK m p i; rewrite addnC n p;
    apply ∧ₑ₂ (leq_add2l p m n) h;
  };
end;

opaque symbol leq_sub m1 m2 n1 n2 :
  π (istrue (m1 ≤ m2)) → π (istrue (n2 ≤ n1)) → π (istrue (m1 - n1 ≤ m2 - n2)) ≔
begin
  assume m1 m2 n1 n2 h i;
  have t:π (istrue (m1 - n1 ≤ m2 - n1)) { apply leq_sub2r m1 m2 n1 h };
  have u:π (istrue (m2 - n1 ≤ m2 - n2)) { apply leq_sub2l n2 n1 m2 i };
  apply @leq_trans (m1 - n1) (m2 - n1) (m2 - n2) t u;
end;

opaque symbol leq_exD n m : π (n ≤ m) → π (`∃ p, n + p = m) ≔
begin
  assume n m h;
  refine ∨ₑ (∧ₑ₁ (leq_eqVlt n m) h) _ _
  { assume heq; refine ∃ᵢ _0 _; simplify; rewrite addn0; refine heq }
  { assume hnltm; refine ∃ᵢ (m - n) _; refine subnKC n m h };
end;

opaque symbol exD_leq n m : π (`∃ p, n + p = m) → π (n ≤ m) ≔
begin
  assume n m h; refine ∃ₑ h _; assume p h2; remove h;
  rewrite left h2; refine leq_addr p n;
end;

// max

symbol max: ℕ → ℕ → ℕ;

rule max _0 $x ↪ $x
with max ($x +1) _0 ↪ $x +1
with max ($x +1) ($y +1) ↪ (max $x $y) +1;

opaque symbol maxn0 x : π (max x _0 = x) ≔
begin
  induction
  { reflexivity }
  { reflexivity}
end;

opaque symbol maxnC x y : π (max x y = max y x) ≔
begin
  induction
  { assume x; rewrite maxn0; reflexivity}
  { assume x h; induction
    { reflexivity }
    { assume y i; simplify; rewrite h; reflexivity }
  }
end;

opaque symbol maxnA x y z : π (max (max x y) z = max x (max y z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite h; reflexivity }
    }
  }
end;

opaque symbol maxnAC x y z : π (max (max x y) z = max (max x z) y) ≔
begin
  assume x y z; rewrite maxnA; rewrite maxnC y z; rewrite left maxnA;
  reflexivity;
end;

opaque symbol maxnCA x y z : π (max x (max y z) = max y (max x z)) ≔
begin
  assume x y z; rewrite left maxnA; rewrite maxnC x y; rewrite maxnA;
  reflexivity;
end;

opaque symbol maxnACA x y z t:
  π (max (max x y) (max z t) = max (max x z) (max y t)) ≔
begin
  assume x y z t; rewrite maxnA; rewrite maxnC y (max z t); rewrite maxnA;
  rewrite left maxnA x z; rewrite maxnC t y; reflexivity;
end;

opaque symbol addn_maxl x y z: π ((max y z) + x = max (y + x) (z + x)) ≔
begin
  induction
  { assume y z; rewrite addn0 (max y z); rewrite addn0 y; rewrite addn0 z; reflexivity }
  { assume x h y z; rewrite addnS (max y z) x; rewrite addnS y x; rewrite addnS z x;
    simplify; apply feq (+1); rewrite h; reflexivity;}
end;

opaque symbol addn_maxr x y z : π (x + (max y z) = max (x + y) (x + z)) ≔
begin
  induction
  { reflexivity }
  { assume x h y z; simplify; apply feq (+1); rewrite h; reflexivity }
end;

opaque symbol subn_maxl x y z: π ( (max x y) - z = max (x - z) (y - z) ) ≔
begin
  induction
  { assume y z; simplify; reflexivity }
  { assume x h; induction
    { assume z; rewrite maxn0; simplify; rewrite maxn0; reflexivity}
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; apply h y z }
    }
  }
end;

opaque symbol maxnE m n : π (max m n = m + (n - m)) ≔
begin
  induction
  { assume n; rewrite subn0; reflexivity }
  { assume m h; induction
    { simplify; rewrite addn0 m; reflexivity }
    { assume n i; simplify; rewrite h; reflexivity }
  }
end;

opaque symbol maxnn x : π (max x x = x) ≔
begin
  induction
  { reflexivity }
  { assume x h; simplify; rewrite h; reflexivity }
end;

opaque symbol leq_maxl m n : π (istrue (m ≤ max m n)) ≔
begin
  induction
  { assume n; apply ⊤ᵢ }
  { assume m h; induction
    { simplify; apply ≤_refl m }
    { assume n i; simplify; apply h n }
  }
end;

opaque symbol leq_maxr m n : π (istrue (n ≤ max m n)) ≔
begin
  assume m n; rewrite maxnC m n; apply leq_maxl n m;
end;

opaque symbol ltn_predK m n : π (istrue (m < n)) → π (n ∸1 +1 = n) ≔
begin
  assume m; induction
  { assume h; refine ⊥ₑ h }
  { reflexivity }
end;

opaque symbol prednK n : π (istrue (_0 < n)) → π (n ∸1 +1 = n) ≔
begin
  refine ltn_predK _0;
end;

opaque symbol leq_pmull m n : π (istrue (n > _0)) → π (istrue (m ≤ n * m)) ≔
begin
  assume m n h;
  have t: π (n ∸1 +1 = n) { apply prednK n h };
  rewrite left t; simplify; apply leq_addr ((n ∸1) * m) m;
end;

opaque symbol leq_pmulr m n : π (istrue (n > _0)) → π (istrue (m ≤ m * n)) ≔
begin
  assume m n h; rewrite mulnC; apply leq_pmull m n h;
end;

opaque symbol leq_mul2l m n1 n2 :
  π (istrue (m * n1 ≤ m * n2) ⇔ (m = _0) ∨ istrue (n1 ≤ n2)) ≔
begin
  assume m n1 n2;
  apply ∧ᵢ {
    assume h;
    have t:π (m * (n1 - n2) = _0) {
      rewrite mulnBr; apply ∧ₑ₂ (subn_eq0 (m * n1) (m * n2)) h;
    };
    have u: π (m = _0 ∨ n1 - n2 = _0) { apply ∧ₑ₁ (muln_eq0 m (n1 - n2)) t };
    apply ∨ₑ u {
      assume i; refine ∨ᵢ₁ i;
    } {
      assume i; apply ∨ᵢ₂; apply ∧ₑ₁ (subn_eq0 n1 n2) i;
    };
  } {
    assume h; apply ∧ₑ₁ (subn_eq0 (m * n1) (m * n2)) _; rewrite left mulnBr;
    apply ∨ₑ h {
      assume i; rewrite i; reflexivity;
    } {
      assume i;
      have t:π (n1 - n2 = _0) { apply ∧ₑ₂ (subn_eq0 n1 n2) i };
      rewrite t; rewrite muln0;reflexivity;
    };
  }
end;

opaque symbol leq_mul2r m n1 n2 :
  π (istrue (n1 * m ≤ n2 * m) ⇔ (m = _0) ∨ (istrue (n1 ≤ n2))) ≔
begin
  assume m n1 n2; rewrite mulnC n1 m; rewrite mulnC n2 m;
  refine leq_mul2l m n1 n2;
end;

opaque symbol leq_mul m1 m2 n1 n2 :
  π (istrue (m1 ≤ n1)) → π (istrue (m2 ≤ n2)) → π (istrue (m1 * m2 ≤ n1 * n2)) ≔
begin
  assume m1 m2 n1 n2 h1 h2;
  have t1:π ((m2 = _0) ∨ istrue (m1 ≤ n1)) { apply ∨ᵢ₂ h1 };
  have t2:π ((n1 = _0) ∨ istrue (m2 ≤ n2)) { apply ∨ᵢ₂ h2 };
  have u1:π (istrue (m1 * m2 ≤ n1 * m2)) { apply ∧ₑ₂ (leq_mul2r m2 m1 n1) t1 };
  have u2:π (istrue (n1 * m2 ≤ n1 * n2)) { apply ∧ₑ₂ (leq_mul2l n1 m2 n2) t2 };
  apply @leq_trans (m1 * m2) (n1 * m2) (n1 * n2) u1 u2;
end;

opaque symbol eqn_mul2l m n1 n2 : π (m * n1 = m * n2 ⇔ (m = _0) ∨ (n1 = n2)) ≔
begin
  assume m n1 n2;
  apply ∧ᵢ {
    assume h;
    have t:π (istrue (m * n1 ≤ m * n2) ∧ istrue (m * n2 ≤ m * n1))
      { apply ∧ₑ₂ (eqn_leq (m * n1) (m * n2)) h };
    have t1:π (istrue (m * n1 ≤ m * n2)) { apply ∧ₑ₁ t };
    have t2:π (istrue (m * n2 ≤ m * n1)) { apply ∧ₑ₂  t };
    have u1: π ((m = _0) ∨ istrue (n1 ≤ n2))
               { apply ∧ₑ₁(leq_mul2l m n1 n2) t1 };
    have u2: π ((m = _0) ∨ istrue (n2 ≤ n1))
               { apply ∧ₑ₁(leq_mul2l m n2 n1) t2 };
    apply ∨ₑ u1 {
      assume i; apply ∨ᵢ₁ i;
    } {
      assume i;
      apply ∨ₑ u2 {
        assume j; apply ∨ᵢ₁ j;
      } {
        assume j; apply ∨ᵢ₂ _;
        apply ∧ₑ₁ (eqn_leq n1 n2) (∧ᵢ i j);
      };
    };
  } {
    assume h;
    apply ∨ₑ h {
      assume i; rewrite i; reflexivity;
    } {
      assume i; rewrite i; reflexivity;
    };
  };
end;

opaque symbol eqn_mul2r m n1 n2 : π ((n1 * m = n2 * m) ⇔ (m = _0) ∨ (n1 = n2)) ≔
begin
  assume m n1 n2; rewrite mulnC n1 m; rewrite mulnC n2 m;
  refine eqn_mul2l m n1 n2;
end;

opaque symbol leq_pmul2l m n1 n2 :
  π (istrue (_0 < m)) → π (istrue (m * n1 ≤ m * n2) ⇔ istrue (n1 ≤ n2)) ≔
begin
  assume m n1 n2 h;
  apply ∧ᵢ {
    assume i;
    have t: π ((m = _0) ∨ istrue (n1 ≤ n2))
              { apply ∧ₑ₁ (leq_mul2l m n1 n2) i };
    apply ∨ₑ t {
      assume j;
      have u: π (istrue (_0 < _0))
                { rewrite left .[m in (istrue (_ < m))] j; apply h };
      refine ⊥ₑ u;
    } {
      assume j; apply j;
    };
  } {
    assume i; refine ∧ₑ₂ (leq_mul2l m n1 n2) _; refine ∨ᵢ₂ i;
  };
end;

opaque symbol leq_pmul2r m n1 n2 :
  π (istrue (_0 < m)) → π (istrue (n1 * m ≤ n2 * m) ⇔ istrue (n1 ≤ n2)) ≔
begin
  assume m n1 n2 h; rewrite mulnC n1 m; rewrite mulnC n2 m;
  refine leq_pmul2l m n1 n2 h;
end;

opaque symbol ltn0_neq0 m : π (istrue (_0 < m) ⇔ m ≠ _0) ≔
begin
  assume m; apply ∧ᵢ {
    generalize m; induction
    { assume h i; apply h }
    { assume m h i j; apply s≠0 j;}
  } {
    generalize m; induction
    { assume h; apply h (eq_refl _0) }
    { assume m h i; apply ⊤ᵢ }
  };
end;

opaque symbol disj0 m : π (m = _0 ∨ m ≠ _0) ≔
begin
  induction
  { apply ∨ᵢ₁ (eq_refl _0) }
  { assume m h; apply ∨ᵢ₂; assume i; apply s≠0 i }
end;

opaque symbol eqn_pmul2l m n1 n2 :
  π (istrue (_0 < m)) → π (m * n1 = m * n2 ⇔ n1 = n2) ≔
begin
  assume m n1 n2 h;
  apply ∧ᵢ {
    assume i1;
    have i2: π (m * n2 = m * n1) { symmetry; apply i1 };
    have v1: π (istrue (m * n1 ≤ m * n2)) { apply eq_leq _ _ i1 };
    have v2: π (istrue (m * n2 ≤ m * n1)) { apply eq_leq _ _ i2 };
    have w1: π (istrue (n1 ≤ n2)) { apply ∧ₑ₁ (leq_pmul2l m n1 n2 h) v1 };
    have w2: π (istrue (n2 ≤ n1)) { apply ∧ₑ₁ (leq_pmul2l m n2 n1 h) v2 };
    apply ∧ₑ₁ (eqn_leq n1 n2) (∧ᵢ w1 w2);
  } {
    assume i;
    have t:π (m = _0 ∨ n1 = n2) { apply ∨ᵢ₂ i };
    apply ∧ₑ₂ (eqn_mul2l m n1 n2) t;
  };
end;

opaque symbol eqn_pmul2r m n1 n2 :
  π (istrue (_0 < m)) → π (n1 * m = n2 * m ⇔ n1 = n2) ≔
begin
  assume m n1 n2 h; rewrite mulnC n1 m; rewrite mulnC n2 m;
  apply eqn_pmul2l m n1 n2 h;
end;

// min

symbol min : ℕ → ℕ → ℕ;

rule min _0 _ ↪ _0
with min (_ +1) _0 ↪ _0
with min ($x +1) ($y +1) ↪ (min $x $y) +1;

opaque symbol minn0 x : π (min x _0 = _0) ≔
begin
  induction
  { reflexivity }
  { reflexivity}
end;

opaque symbol minnC x y : π (min x y = min y x) ≔
begin
  induction
  { assume x; rewrite minn0; reflexivity}
  { assume x h; induction
    { reflexivity }
    { assume y i; simplify; rewrite h; reflexivity }
  }
end;

opaque symbol minnA x y z : π (min (min x y) z = min x (min y z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite h; reflexivity;}
    }
  }
end;

opaque symbol minnAC x y z : π (min (min x y) z = min (min x z) y) ≔
begin
  assume x y z; rewrite minnA; rewrite minnC y z; rewrite left minnA;
  reflexivity;
end;

opaque symbol minnCA x y z : π (min x (min y z) = min y (min x z)) ≔
begin
  assume x y z; rewrite left minnA; rewrite minnC x y; rewrite minnA;
  reflexivity;
end;

opaque symbol minnACA x y z t :
  π (min (min x y) (min z t) = min (min x z) (min y t)) ≔
begin
  assume x y z t; rewrite minnA; rewrite minnC y (min z t); rewrite minnA;
  rewrite left minnA x z; rewrite minnC t y; reflexivity;
end;

opaque symbol addn_minl x y z: π ((min y z) + x = min (y + x) (z + x)) ≔
begin
  induction
  { assume y z; rewrite addn0 (min y z); rewrite addn0 y; rewrite addn0 z; reflexivity }
  { assume x h y z; rewrite addnS (min y z) x; rewrite addnS y x; rewrite addnS z x;
    simplify; apply feq (+1); rewrite h; reflexivity;}
end;

opaque symbol addn_minr x y z: π (x + (min y z) = min (x + y) (x + z)) ≔
begin
  induction
  { reflexivity }
  { assume x h y z; simplify; apply feq (+1); rewrite h; reflexivity;}
end;

opaque symbol subn_minl x y z: π ((min x y) - z = min (x - z) (y - z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { assume z; simplify; rewrite minn0; reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; apply h y z }
    }
  }
end;

opaque symbol minnn x : π (min x x = x) ≔
begin
  induction
  { reflexivity;}
  { assume x h; simplify; rewrite h; reflexivity }
end;

opaque symbol geq_minl m n : π (istrue (min m n ≤ m)) ≔
begin
  induction
  { assume n; apply ⊤ᵢ }
  { assume m h; induction
    { apply ⊤ᵢ }
    { assume n i; simplify; apply h n }
  }
end;

opaque symbol geq_minr m n : π (istrue (min m n ≤ n)) ≔
begin
  assume m n; rewrite minnC; apply geq_minl n m;
end;

// proofs on max and min

opaque symbol addn_min_max m n : π (min m n + max m n = m + n) ≔
begin
  induction
  { reflexivity }
  { assume m h; induction
    { rewrite addn0 (m +1); reflexivity }
    { assume n i; simplify; rewrite addnS (min m n) (max m n);      rewrite addnS m n; rewrite h n; reflexivity }
  }
end;

opaque symbol maxnK m n : π (min (max m n) m = m) ≔
begin
  induction
  { assume n; rewrite minn0; reflexivity }
  { assume m h; induction
    { simplify; rewrite minnn; reflexivity }
    { assume n i; simplify; rewrite h n; reflexivity }
  }
end;

opaque symbol maxKn m n : π (min n (max m n) = n) ≔
begin
  induction
  { assume n; simplify; rewrite minnn; reflexivity }
  { assume m h; induction
    { reflexivity }
    { assume n i; simplify; rewrite h n; reflexivity }
  }
end;

opaque symbol minnK m n : π (max (min m n) m = m) ≔
begin
  induction
  { reflexivity }
  { assume m h; induction
    { reflexivity }
    { assume n i; simplify; rewrite h n; reflexivity }
  }
end;

opaque symbol minKn m n : π (max n (min m n) = n) ≔
begin
  induction
  { assume n; simplify; rewrite maxn0; reflexivity }
  { assume m h; induction
    { reflexivity }
    { assume n i; simplify; rewrite h n; reflexivity }
  }
end;

opaque symbol maxn_minl x y z : π (max x (min y z) = min (max x y) (max x z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { assume z; simplify; rewrite minnC; rewrite maxnK (x +1) z; reflexivity }
    { assume y i; induction
      { simplify; rewrite maxnK x y; reflexivity }
      { assume z j; simplify; rewrite h; reflexivity }
    }
  }
end;

opaque symbol maxn_minr x y z : π (max (min y z) x = min (max y x) (max z x)) ≔
begin
  induction
  { assume y z; rewrite maxn0; rewrite maxn0; rewrite maxn0; reflexivity }
  { assume x h; induction
    { assume z; simplify; rewrite maxKn z (x +1); reflexivity }
    { assume y i; induction
      { simplify; rewrite maxnC; rewrite maxnK x y; reflexivity }
      { assume z j; simplify; rewrite h; reflexivity }
    }
  }
end;

opaque symbol minn_maxl x y z : π (min x (max y z) = max (min x y) (min x z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite h; reflexivity }
    }
  }
end;

opaque symbol minn_maxr x y z : π (min (max y z) x = max (min y x) (min z x)) ≔
begin
  induction
  { assume y z; rewrite minn0; rewrite minn0; rewrite minn0; reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; simplify; rewrite h; reflexivity }
    }
  }
end;

opaque symbol maxnMr x y z : π ((max y z) * x = max (y * x) (z * x)) ≔
begin
  induction
  { assume y z; rewrite muln0; rewrite muln0; rewrite muln0;  reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z;
        rewrite left addn_maxl (_0 +1) y z; symmetry;
        rewrite mulnDl y (_0 +1) (x +1); rewrite mulnDl z (_0 +1) (x +1);
        rewrite left addn_maxl ((_0 +1) * (x +1)) (y * (x +1)) (z * (x +1));
        rewrite left i; symmetry; rewrite mulnDl (max y z) (_0 +1) (x +1);
        reflexivity;
      }
    }
  }
end;

opaque symbol maxnMl x y z : π (x * (max y z) = max (x * y) (x * z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { assume z; rewrite muln0; reflexivity }
    { assume y i; induction
      { rewrite muln0; reflexivity}
      { assume z j; rewrite left addn1 y; rewrite left addn1 z;
        rewrite left addn_maxl (_0 +1) y z; symmetry;
        rewrite mulnDr y (_0 +1) (x +1); rewrite mulnDr z (_0 +1) (x +1);
        rewrite left addn_maxl ((x +1) * (_0 +1)) ((x +1) * y) ((x +1) * z);
        rewrite left i; symmetry; rewrite mulnDr (max y z) (_0 +1) (x +1);
        reflexivity;
      }
    }
  }
end;

opaque symbol minnMr x y z : π ((min y z) * x = min (y * x) (z * x)) ≔
begin
  induction
  { assume y z; rewrite muln0; rewrite muln0; reflexivity }
  { assume x h; induction
    { reflexivity }
    { assume y i; induction
      { reflexivity }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z;
        rewrite left addn_minl (_0 +1) y z; symmetry;
        rewrite mulnDl y (_0 +1) (x +1); rewrite mulnDl z (_0 +1) (x +1);
        rewrite left addn_minl ((_0 +1) * (x +1)) (y * (x +1)) (z * (x +1));
        rewrite left i; symmetry; rewrite mulnDl (min y z) (_0 +1) (x +1);
        reflexivity;
      }
    }
  }
end;

opaque symbol minnMl x y z : π (x * (min y z) = min (x * y) (x * z)) ≔
begin
  induction
  { reflexivity }
  { assume x h; induction
    { assume z; rewrite muln0; simplify; rewrite muln0; reflexivity }
    { assume y i; induction
      { rewrite muln0; simplify; rewrite muln0; reflexivity }
      { assume z j; rewrite left addn1 y; rewrite left addn1 z;
        rewrite left addn_minl (_0 +1) y z; symmetry;
        rewrite mulnDr y (_0 +1) (x +1); rewrite mulnDr z (_0 +1) (x +1);
        rewrite left addn_minl ((x +1) * (_0 +1)) ((x +1) * y) ((x +1) * z);
        rewrite left i; symmetry; rewrite mulnDr (min y z) (_0 +1) (x +1);
        reflexivity;
      }
    }
  }
end;

// exponentiation

symbol ^ : ℕ → ℕ → ℕ; notation ^ infix left 40;

rule _ ^ _0 ↪ _0 +1
with $n ^ ($m +1) ↪ $n * $n ^ $m;

opaque symbol expn0 m : π (m ^ _0 = _0 +1) ≔
begin
  reflexivity;
end;

opaque symbol expn m : π (m ^ (_0 +1) = m) ≔
begin
  assume m; simplify; rewrite mulnS; rewrite muln0 m; rewrite addn0 m; reflexivity;
end;

opaque symbol expnS a n : π (a ^ (n +1) = a * a ^ n ) ≔
begin
  assume a; induction
  { reflexivity }
  { reflexivity;}
end;

opaque symbol expnSr a n : π (a ^ (n +1) = a ^ n * a) ≔
begin
  assume a n; rewrite expnS a n; rewrite mulnC; reflexivity;
end;

opaque symbol exp0n n : π (istrue (_0 < n)) → π (_0 ^ n = _0) ≔
begin
  induction
  { assume h; refine ⊥ₑ h;}
  { reflexivity }
end;

opaque symbol exp1n n : π ((_0 +1) ^ n = (_0 +1)) ≔
begin
  induction
  { reflexivity }
  { assume n h; simplify; rewrite h; reflexivity }
end;

opaque symbol expnD a m n: π (a ^ (m + n) = a ^ m * a ^ n) ≔
begin
  assume a; induction
  { assume n; rewrite add0n n; rewrite expn0 a; rewrite mul1n (a ^ n); reflexivity }
  { assume m h n; simplify; rewrite h n; rewrite mulnA; reflexivity }
end;

opaque symbol expnMn m1 m2 n : π ((m1 * m2) ^ n = m1 ^ n * m2 ^ n) ≔
begin
  assume m1 m2; induction
  { reflexivity }
  { assume n h;  simplify; rewrite h; rewrite mulnA; rewrite mulnA;
    rewrite left mulnA (m1 ^ n) m2; rewrite mulnC (m1 ^ n) m2;
    rewrite mulnA m2 (m1 ^ n); reflexivity;
  }
end;

opaque symbol expnM m n1 n2 : π (m ^ (n1 * n2) = (m ^ n1) ^ n2) ≔
begin
  assume m; induction
  { assume n2; simplify; rewrite exp1n; reflexivity }
  { assume n1 h n2; simplify; rewrite expnD; rewrite h n2;
    rewrite left expnMn; reflexivity }
end;

opaque symbol expnAC m n1 n2 : π ((m ^ n1) ^ n2 = (m ^ n2) ^ n1) ≔
begin
  assume m n1 n2; rewrite left expnM; rewrite mulnC; rewrite expnM;
  reflexivity;
end;

// factorial

symbol ! : ℕ → ℕ; notation ! postfix 40;

rule _0 ! ↪ _0 +1
with ($n +1) ! ↪ ($n +1) * $n !;

opaque symbol fact0 : π (_0 ! = (_0 +1)) ≔
begin
  reflexivity;
end;

opaque symbol factS n : π ((n +1) ! = n +1 * n !) ≔
begin
  reflexivity;
end;

opaque symbol fact_gt0 n : π (istrue (n ! > _0)) ≔
begin
  induction
  { apply ⊤ᵢ }
  { assume n h; rewrite factS n; rewrite mulSnr n (n !);
    apply ltn_addl _0 (n !) (n * n !); apply h }
end;

opaque symbol fact_gt1 n : π (istrue (n ! ≥ _0 +1)) ≔
begin
  refine fact_gt0;
end;

opaque symbol fact_geq n : π (istrue (n ≤ n !)) ≔
begin
  induction
  { apply ⊤ᵢ }
  { assume n h; rewrite factS n; apply leq_pmulr (n +1) (n !) (fact_gt0 n) }
end;


// Division by two i.e half

symbol div2 : ℕ → ℕ;
rule div2 _0 ↪ _0
with div2 (_0 +1) ↪ _0
with div2 (($x +1) +1) ↪ (div2 $x) +1;

opaque symbol mul2n n : π (2 * n = n + n) ≔
begin
  assume n; rewrite mulnC; refine muln2 n
end;

opaque symbol div2_addnn x : π (div2 (x + x) = x) ≔
begin
  induction
  {reflexivity}
  { assume x ih; simplify; rewrite addnS; apply feq (+1); apply ih }
end;

opaque symbol div2_mul2n x : π ((div2 (2 * x)) = x) ≔
begin
  assume x; rewrite mul2n; refine div2_addnn x
end;

opaque symbol div2_addnnS x : π (div2 ((x + x) +1) = x) ≔
begin
  induction
  {reflexivity}
  { assume x ih; simplify; rewrite addnS; apply feq (+1); apply ih }
end;

opaque symbol div2_mul2nS n : π ( div2 ((2 * n) +1) = n) ≔
begin
  assume n; rewrite mul2n; refine div2_addnnS n
end;

opaque symbol leq_div2 n : π (div2 (n) ≤ n) ≔
begin
  refine ind_ℕ2 (λ u, istrue (div2 u ≤ u)) _ _ _
  {apply ⊤ᵢ }
  {apply ⊤ᵢ }
  {
    assume x;
    assume ih ih2;
    apply @leq_trans (div2 x) x (x +1)
    {refine ih}
    {
      refine leqnSn x
    }
  }
end;

opaque symbol leq_div2Sn n : π (div2 (n +1) ≤ n) ≔
begin
  induction
  {apply ⊤ᵢ }
  { assume x ih; refine leq_div2 x }
end;

opaque symbol leq_div2_leqS a n : π (a ≤ n +1) → π (div2 a ≤ n) ≔
begin
  induction
  { assume n h; apply ⊤ᵢ }
  {
    assume a ih n h;
    apply @leq_trans (div2 (a +1)) a n (leq_div2Sn a) h
  }
end;

// div2 recovers the number from its parity

opaque symbol even_div2 n : π (even n) → π (div2 n + div2 n = n) ≔
begin
  refine ind_ℕ2 (λ u, istrue (even u) ⇒ (div2 u + div2 u = u)) _ _ _
  { reflexivity }
  { assume h; apply ⊥ₑ h }
  { assume x ihx ihx1 h; simplify; rewrite addnS; rewrite ihx h; reflexivity }
end;

opaque symbol odd_div2 n : π (odd n) → π ((div2 n + div2 n) +1 = n) ≔
begin
  refine ind_ℕ2 (λ u, istrue (odd u) ⇒ ((div2 u + div2 u) +1 = u)) _ _ _
  { assume h; apply ⊥ₑ h }
  { reflexivity }
  { assume x ihx ihx1 h; simplify; rewrite addnS; rewrite ihx h; reflexivity }
end;

// Bitwise operations

symbol double x ≔ x + x;

// shift left
// left-shifting a natural `x` with a natural `y` is equivalent to multiplying `x` by 2 raised to power `y`.
symbol <<<: ℕ → ℕ → ℕ; notation <<< infix 30;
rule $x <<< 0 ↪ $x
with $x <<< ($n +1) ↪ double ($x <<< $n);

symbol <<: ℕ → ℕ ≔ λ x, x <<< 1 ; notation << postfix 30;

assert ⊢ 21 <<< 1 ≡ 42;

// shift right
// x >>> y ↪ x / (2 ^ y)
symbol >>>: ℕ → ℕ → ℕ; notation >>> infix 30;
rule $x >>> 0 ↪ $x
with $x >>> ($n +1) ↪ div2 ($x >>> $n);

symbol >>: ℕ → ℕ ≔ λ x, x >>> 1 ; notation >> postfix 30;

assert ⊢ 21 >>> 2 ≡ 5;

symbol bitwise : (𝔹 → 𝔹 → 𝔹) → ℕ → ℕ → ℕ → ℕ;

rule bitwise _ _0 _ _ ↪ _0
with bitwise $op ($n +1) $a $b ↪
  (if ($op (odd $a) (odd $b)) 1 0) + 2 * bitwise $op $n (div2 $a) (div2 $b);

symbol && (a b: ℕ): ℕ ≔ bitwise (and) a a b; notation && infix 10;

symbol ⎪⎪ (a b: ℕ): ℕ ≔ bitwise (or) (max a b) a b; notation ⎪⎪ infix 12;

assert ⊢ 2 ⎪⎪ 8 ≡ 10;

symbol diff (a b: ℕ): ℕ ≔ bitwise (λ b1, λ b2,  b1 and (not b2)) a a b;

symbol xor (a b: ℕ): ℕ ≔ bitwise (xorb) (max a b) a b; notation xor infix 10;

symbol testbit (a n: ℕ) : 𝔹;
rule testbit $a 0 ↪ odd $a
with testbit $a ($n +1) ↪ testbit (div2 $a) $n;

symbol testbit_0_l n : π (testbit 0 n = false) ≔
begin induction { reflexivity } { assume x ih; apply ih } end;

symbol Odd n ≔ (`∃ k, (2 * k + 1) = n);

symbol Odd2 n : π (Odd n) → π (Odd (n + 2));

symbol odd_spec n : π (Odd n) → π (odd n = true);

symbol Even n ≔ (`∃ k, 2 * k = n);

symbol even_spec n : π (Even n) → π (even n = true);

symbol odd_bitwise op n a b : π (odd (bitwise op (n +1) a b) = op (odd a) (odd b)) ≔
begin
  assume op n a b;
  simplify bitwise;
  have case: π (
    (op (odd a) (odd b) = true)
    ∨
    (op (odd a) (odd b) = false)) { apply case_𝔹 };
  apply ∨ₑ case
  {
    assume hl; rewrite hl; simplify if;
    rewrite addnC;
    apply odd_spec ((_2 * bitwise op n (div2 a) (div2 b)) + _1);
    apply ∃ᵢ (bitwise op n (div2 a) (div2 b));
    reflexivity
  }
  {
    assume hr; rewrite hr; simplify if;
    simplify; rewrite addn0;
    refine @feq bool bool not (even (bitwise op n (div2 a) (div2 b) + bitwise op n (div2 a) (div2 b))) true _;
    apply even_spec (bitwise op n (div2 a) (div2 b) + bitwise op n (div2 a) (div2 b));
    refine ∃ᵢ (bitwise op n (div2 a) (div2 b)) (mul2n (bitwise op n (div2 a) (div2 b)))
  }
end;

symbol div2_bitwise op n a b :
  π (div2 (bitwise op (n +1) a b) = bitwise op n (div2 a) (div2 b)) ≔
begin
  assume op n a b;
  simplify bitwise;
  have case: π (
    (op (odd a) (odd b) = true)
    ∨
    (op (odd a) (odd b) = false)) { apply case_𝔹 };
  apply ∨ₑ case
  {
    assume hl; rewrite hl; simplify if;
    rewrite addnC; simplify; rewrite addn1;
    apply div2_mul2nS
  }
  {
    assume hr; rewrite hr; simplify if;
    apply div2_mul2n (bitwise op n (div2 a) (div2 b))
  }
end;

symbol testbit_bitwise_1 op (hop : Π b, π (op false b = false)) n m a b :
  π (a ≤ n) →
  π (testbit (bitwise op n a b) m = op (testbit a m) (testbit b m))
≔ begin
  assume op Hop;
  induction
  {
     assume m a b Ha;
    rewrite ≤0 a Ha;
    simplify;
    rewrite testbit_0_l;
    rewrite Hop ((testbit b m));
    reflexivity
  }
  {
    assume n IHn;
    induction
    {
      assume a b ha;
      apply odd_bitwise op (n) a b
    }
    {
      assume m Ihm a b ha;
      simplify testbit;
      rewrite div2_bitwise;
      apply IHn m (div2 a) (div2 b) _;
      refine  leq_div2_leqS a n ha
    }
  }
end;

symbol testbit_bitwise_2 op (hop : π (op false false = false)) n m a b :
  π (a ≤ n) → π (b ≤ n) →
  π (testbit (bitwise op n a b) m = op (testbit a m) (testbit b m))
≔ begin
  assume op Hop_spec;
  induction
  {
     assume m a b Ha Hb;
    rewrite ≤0 a Ha;
    rewrite ≤0 b Hb;
    simplify;
    rewrite testbit_0_l;
    symmetry;
    apply Hop_spec
  }
  {
    assume n IHn;
    induction
    {
      assume a b ha hb;
      apply odd_bitwise op (n) a b;
    }
    {
      assume m Ihm a b ha hb;
      simplify testbit;
      rewrite div2_bitwise;
      apply IHn m (div2 a) (div2 b) _ _
      { refine  leq_div2_leqS a n ha }
      { refine  leq_div2_leqS b n hb }
    }
  }
end;

symbol land_spec a b n :
  π (testbit (a && b) n = (testbit a n and testbit b n)) ≔
begin
  assume a n b;
  simplify;
  refine testbit_bitwise_1 (and) _ a b a n (≤_refl a);
  induction
  {reflexivity}
  {reflexivity}
end;

symbol ldiff_spec a b n :
  π (testbit (diff a b) n = (testbit a n and not (testbit b n))) ≔
begin
  assume a n b;
  simplify diff;
  refine testbit_bitwise_1 (λ a b, a and not b) _ a b a n (≤_refl a);
  induction
  {reflexivity}
  {reflexivity}
end;

symbol lor_spec a b n :
  π (testbit (a ⎪⎪ b) n = (testbit a n or testbit b n)) ≔
begin
  assume a n b;
  simplify;
  refine  testbit_bitwise_2 (or) _ (max a n) b a n _ _
  {reflexivity}
  {refine leq_maxl a n }
  {refine leq_maxr a n }
end;

symbol xor_spec a b n :
  π (testbit (a xor b) n = (testbit a n xorb testbit b n)) ≔
begin
 assume a n b;
  simplify;
  refine  testbit_bitwise_2 (xorb) _ (max a n) b a n _ _
  {reflexivity}
  {refine leq_maxl a n }
  {refine leq_maxr a n }
end;

opaque symbol shiftr_spec a n m : π (testbit (a >>> n) m = testbit a (m + n)) ≔
begin
  assume a;
  induction
  { assume m; rewrite addn0; reflexivity }
  {
    assume n ihn m;
    rewrite addnS;
    refine ihn (m +1)
  }
end;

opaque symbol shiftl_spec a n m : π (n ≤ m) → π (testbit (a <<< n) m = testbit a (m - n)) ≔
begin
assume a;
  induction
  { assume m h; rewrite subn0; reflexivity }
  {
    assume n ih;
    induction
    {
      assume contra;
      apply ⊥ₑ contra
    }
    {
      assume m ihm h;
      remove ihm;
      simplify;
      rewrite left (ih m h);
      have g: π ((((a <<< n) + (a <<< n))) = (2 * (a <<< n)))
        { symmetry; refine mul2n (a <<< n) };
      rewrite g;
      rewrite div2_mul2n;
      reflexivity
    }
  }
end;

// Strong (course-of-values) induction

opaque symbol ind_ℕ_strong (p : ℕ → Prop) :
  (Π n, (Π m, π (istrue (m < n)) → π (p m)) → π (p n)) → Π n, π (p n) ≔
begin
  assume p ih n;
  have aux : Π k, Π m, π (istrue (m ≤ k)) → π (p m)
  { induction
    { assume m h; rewrite ≤0 m h; refine ih _0 _;
      assume m' h'; apply ⊥ₑ; refine ltn0 m' h' }
    { assume k rec m h; refine ih m _;
      assume m' h'; refine rec m' (@leq_trans (m' +1) m (k +1) h' h) } };
  refine aux n n (≤_refl n)
end;
