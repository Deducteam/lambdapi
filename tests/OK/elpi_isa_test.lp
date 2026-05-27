
/* Encoding of simple type theory */
constant symbol Set : TYPE;
constant symbol bool : Set;
constant symbol fun : Set → Set → Set;
injective symbol El : Set → TYPE;
rule El (fun $a $b) ↪ El $a → El $b;
injective symbol Prf : El bool → TYPE;

/* HOL-Light primitive constants, axioms and rules */
constant symbol = [A] : El (fun A (fun A bool)); notation = infix 50;
symbol el [A] : El A;
symbol ε [A] : El (fun (fun A bool) A); notation ε quantifier;
symbol fun_ext [a b] [f g : El (fun a b)] :
  (Π x, Prf ((f x) = (g x))) → Prf (f = g);
symbol prop_ext [p q : El bool] : (Prf p → Prf q) → (Prf q → Prf p) → Prf (p = q);
symbol REFL [a] (t : El a) : Prf (t = t);
symbol MK_COMB [a b] [s t : El (fun a b)] [u v : El a] :
  Prf (s = t) → Prf (u = v) → Prf ((s u) = (t v));
symbol EQ_MP [p q : El bool] : Prf (p = q) → Prf p → Prf q;
opaque symbol TRANS [a] [x y z : El a] (xy: Prf (x = y)) (yz: Prf (y = z))
  : Prf (x = z) ≔
@EQ_MP (@= a x y) (@= a x z) (@MK_COMB a bool (@= a x) (@= a x) y z (@REFL (fun a bool) (@= a x)) yz) xy;
opaque symbol SYM [a] [x y : El a] (xy: Prf (x = y)) : Prf (y = x) ≔
@EQ_MP (@= a x x) (@= a y x) (@MK_COMB a bool (@= a x) (@= a y) x x (@MK_COMB a (fun a bool) (@= a) (@= a) x y (@REFL (fun a (fun a bool)) (@= a)) xy) (@REFL a x)) (@REFL a x);

builtin "T"     ≔ El; // : U → TYPE
builtin "P"     ≔ Prf; // : Prop → TYPE
builtin "eq"    ≔ =; // : Π [a], T a → T a → Prop
builtin "refl"  ≔ REFL; // : Π [a] (x:T a), P(x = x)
symbol eq_ind : Π [a] x y, Prf (x = y) → Π p:El a → El bool, Prf (p y) → Prf (p x) ≔ begin
  assume a x y eqxy p py;
  refine (EQ_MP _ py);
  apply (MK_COMB (REFL p));
  apply (SYM eqxy);
end;
builtin "eqind" ≔ eq_ind; // : Π [a] x y, P(x = y) → Π p:T a → Prop, P(p y) → P(p x)

/* HOL-Light derived connectives */
constant symbol ∃₁ [A] : El (fun (fun A bool) bool); notation ∃₁ quantifier;
constant symbol ¬ : El (fun bool bool); notation ¬ prefix 30;
constant symbol ⊥ : El bool;
constant symbol ∨ : El (fun bool (fun bool bool)); notation ∨ infix left 25;
constant symbol ∃ [A] : El (fun (fun A bool) bool); notation ∃ quantifier;
constant symbol ∀ [A] : El (fun (fun A bool) bool); notation ∀ quantifier;
constant symbol ⇒ : El (fun bool (fun bool bool)); notation ⇒ infix right 15;
constant symbol ∧ : El (fun bool (fun bool bool)); notation ∧ infix left 20;
constant symbol ⊤ : El bool;

/* Natural deduction rules */
rule Prf (⇒ $p $q) ↪ Prf $p → Prf $q;
rule Prf (∀ $p) ↪ Π x, Prf ($p x);
symbol ⊤ᵢ : Prf ⊤;
symbol ∧ᵢ [p : El bool] : Prf p → Π [q : El bool], Prf q → Prf (p ∧ q);
symbol ∧ₑ₁ [p q : El bool] : Prf (p ∧ q) → Prf p;
symbol ∧ₑ₂ [p q : El bool] : Prf (p ∧ q) → Prf q;
symbol ∃ᵢ [a] (p : El a → El bool) t : Prf (p t) → Prf (`∃ x, p x);
symbol ∃ₑ [a] [p : El a → El bool] : Prf (`∃ x, p x) → Π [r : El bool], (Π x:El a, Prf (p x) → Prf r) → Prf r;
symbol ∨ᵢ₁ [p : El bool] : Prf p → Π q : El bool, Prf (p ∨ q);
symbol ∨ᵢ₂ (p : El bool) [q : El bool] : Prf q → Prf (p ∨ q);
symbol ∨ₑ [p q : El bool] :
  Prf (p ∨ q) → Π [r], (Prf p → Prf r) → (Prf q → Prf r) → Prf r;

injective typeclass symbol zero_class : Set → TYPE;
constant symbol mk_zero [A : Set] : El A → zero_class A;
symbol _0 [A : Set] [B : zero_class A] : El A;
rule @_0 _ (mk_zero $zero) ↪ $zero;

injective typeclass symbol one_class : Set → TYPE;
constant symbol mk_one [A : Set] : El A → one_class A;
symbol _1 [A : Set] [B : one_class A] : El A;
rule @_1 _ (mk_one $one) ↪ $one;

injective typeclass symbol plus_class : Set → TYPE;
constant symbol mk_plus [A : Set] : El (fun A (fun A A)) → plus_class A;
symbol + [A : Set] [B : plus_class A] : El (fun A (fun A A)); notation + infix left 65;
rule @+ _ (mk_plus $add) ↪ $add;

injective typeclass symbol minus_class : Set → TYPE;
constant symbol mk_minus [A : Set] : El (fun A (fun A A)) → minus_class A;
symbol - [A : Set] [B : minus_class A] : El (fun A (fun A A)); notation - infix left 65;
rule @- _ (mk_minus $sub) ↪ $sub;

injective typeclass symbol uminus_class : Set → TYPE;
constant symbol mk_uminus [A : Set] : El (fun A A) → uminus_class A;
symbol — [A : Set] [B : uminus_class A] : El (fun A A); notation — prefix 80;
rule @— _ (mk_uminus $opp) ↪ $opp;

injective typeclass symbol times_class : Set → TYPE;
constant symbol mk_times [A : Set] : El (fun A (fun A A)) → times_class A;
symbol * [A : Set] [B : times_class A] : El (fun A (fun A A)); notation * infix left 70;
rule @* _ (mk_times $mul) ↪ $mul;

injective typeclass symbol semigroup_add_class : Set → TYPE;
constant symbol mk_semigroup_add [A : Set] [B : plus_class A] : Prf (`∀ a, `∀ b, `∀ c, ((a + b) + c = a + (b + c))) → semigroup_add_class A;

//PROBLEM: last instance defined will be used by default even without typing info:
//instance symbol test : plus_class bool;
//symbol test2 ≔ _ + _ (typechecker: The proof is not finished (then shows goals of type El bool));

instance symbol plus_of_semigroup_add [A : Set] : semigroup_add_class A → plus_class A;
rule @plus_of_semigroup_add _ (@mk_semigroup_add _ $prf _) ↪ $prf;

symbol add_assoc [A : Set] [B : semigroup_add_class A] : Prf (`∀ a, `∀ b, `∀ c, ((a + b) + c = a + (b + c)));
//probably useless to declare a rule for it

injective typeclass symbol ab_semigroup_add_class : Set → TYPE;
constant symbol mk_ab_semigroup_add [A : Set] [B : semigroup_add_class A] : Prf (`∀ a, `∀ b, a + b = b + a) → ab_semigroup_add_class A;

instance symbol semigroup_add_of_ab_semigroup_add [A : Set] : ab_semigroup_add_class A → semigroup_add_class A;
rule @semigroup_add_of_ab_semigroup_add _ (@mk_ab_semigroup_add _ $prf _) ↪ $prf;

symbol add_commute [A : Set] [B : ab_semigroup_add_class A] : Prf (`∀ a, `∀ b, a + b = b + a);

injective typeclass symbol semigroup_mult_class : Set → TYPE;
constant symbol mk_semigroup_mult [A : Set] [B : times_class A] : Prf (`∀ a, `∀ b, `∀ c, ((a * b) * c = a * (b * c))) → semigroup_mult_class A;

instance symbol times_of_semigroup_mult [A : Set] : semigroup_mult_class A → times_class A;
rule @times_of_semigroup_mult _ (@mk_semigroup_mult _ $prf _) ↪ $prf;

symbol mult_assoc [A : Set] [B : semigroup_mult_class A] : Prf (`∀ a, `∀ b, `∀ c, ((a * b) * c = a * (b * c)));

injective typeclass symbol ab_semigroup_mult_class : Set → TYPE;
constant symbol mk_ab_semigroup_mult [A : Set] [B : semigroup_mult_class A] : Prf (`∀ a, `∀ b, a * b = b * a) → ab_semigroup_mult_class A;

instance symbol semigroup_mult_of_ab_semigroup_mult [A : Set] : ab_semigroup_mult_class A → semigroup_mult_class A;
rule @semigroup_mult_of_ab_semigroup_mult _ (@mk_ab_semigroup_mult _ $prf _) ↪ $prf;

symbol mult_commute [A : Set] [B : ab_semigroup_mult_class A] : Prf (`∀ a, `∀ b, a * b = b * a);

injective typeclass symbol monoid_add_class : Set → TYPE;
constant symbol mk_monoid_add [A : Set] [B : zero_class A] [C : semigroup_add_class A] :
  Prf (`∀ a, _0 + a = a) → Prf (`∀ a, a + _0 = a) → monoid_add_class A;

instance symbol zero_of_monoid_add [A : Set] : monoid_add_class A → zero_class A;
rule @zero_of_monoid_add _ (@mk_monoid_add _ $prf _ _ _) ↪ $prf;

instance symbol semigroup_add_of_monoid_add [A : Set] : monoid_add_class A → semigroup_add_class A;
rule @semigroup_add_of_monoid_add _ (@mk_monoid_add _ _ $prf _ _) ↪ $prf;

symbol add_0_left [A : Set] [B : monoid_add_class A] : Prf (`∀ a, _0 + a = a);
symbol add_0_right [A : Set] [B : monoid_add_class A] : Prf (`∀ a, a + _0 = a);

injective typeclass symbol comm_monoid_add_class : Set → TYPE;
constant symbol mk_comm_monoid_add [A : Set] [B : zero_class A] [C : ab_semigroup_add_class A] :
  Prf (`∀ a, _0 + a = a) → comm_monoid_add_class A;

instance symbol zero_of_comm_monoid_add [A : Set] : comm_monoid_add_class A → zero_class A;
rule @zero_of_comm_monoid_add _ (@mk_comm_monoid_add _ $prf _ _) ↪ $prf;

instance symbol ab_semigroup_add_of_comm_monoid_add [A : Set] : comm_monoid_add_class A → ab_semigroup_add_class A;

opaque symbol SYME [A : Set] [x y : El A] : Prf ((x = y) = (y = x)) ≔ begin
  assume A x y ; apply prop_ext
  {
    assume e; symmetry; refine e;
  }
  {
    assume e; symmetry ; refine e;
  }
end;

opaque symbol zero_reorient [A : Set] [B : monoid_add_class A] : Prf (`∀ x, (_0 = x) = (x = _0)) ≔ begin
  assume A B x; refine SYME;
end;

//TODO: report later: adding an extra underscore after mk_comm_monoid_add triggers the wrong error message.
rule @ab_semigroup_add_of_comm_monoid_add _ (@mk_comm_monoid_add _ _ $prf _) ↪ $prf;

symbol add_0 [A : Set] [B : comm_monoid_add_class A] : Prf (`∀ a, _0 + a = a);

instance symbol monoid_add_of_comm_monoid_add [A : Set] [B : comm_monoid_add_class A] : monoid_add_class A ≔
  mk_monoid_add add_0 (λ a, TRANS (add_commute a _0) (add_0 a));

injective typeclass symbol monoid_mult_class : Set → TYPE;
constant symbol mk_monoid_mult [A : Set] [B : one_class A] [C : semigroup_mult_class A] :
  Prf (`∀ a, _1 * a = a) → Prf (`∀ a, a * _1 = a) → monoid_mult_class A;

instance symbol one_of_monoid_mult [A : Set] : monoid_mult_class A → one_class A;
rule @one_of_monoid_mult _ (@mk_monoid_mult _ $prf _ _ _) ↪ $prf;

instance symbol semigroup_mult_of_monoid_mult [A : Set] : monoid_mult_class A → semigroup_mult_class A;
rule @semigroup_mult_of_monoid_mult _ (@mk_monoid_mult _ _ $prf _ _) ↪ $prf;

symbol mult_1_left [A : Set] [B : monoid_mult_class A] : Prf (`∀ a, _1 * a = a);
symbol mult_1_right [A : Set] [B : monoid_mult_class A] : Prf (`∀ a, a * _1 = a);

injective typeclass symbol comm_monoid_mult_class : Set → TYPE;
constant symbol mk_comm_monoid_mult [A : Set] [B : one_class A] [C : ab_semigroup_mult_class A] :
  Prf (`∀ a, _1 * a = a) → comm_monoid_mult_class A;

instance symbol one_of_comm_monoid_mult [A : Set] : comm_monoid_mult_class A → one_class A;
rule @one_of_comm_monoid_mult _ (@mk_comm_monoid_mult _ $prf _ _) ↪ $prf;

instance symbol ab_semigroup_mult_of_comm_monoid_mult [A : Set] : comm_monoid_mult_class A → ab_semigroup_mult_class A;

opaque symbol one_reorient [A : Set] [B : monoid_mult_class A] : Prf (`∀ x, (_1 = x) = (x = _1)) ≔ begin
  assume A B x; refine SYME;
end;

rule @ab_semigroup_mult_of_comm_monoid_mult _ (@mk_comm_monoid_mult _ _ $prf _) ↪ $prf;

symbol mult_1 [A : Set] [B : comm_monoid_mult_class A] : Prf (`∀ a, _1 * a = a);

instance symbol monoid_mult_of_comm_monoid_mult [A : Set] [B : comm_monoid_mult_class A] : monoid_mult_class A ≔
  mk_monoid_mult mult_1 (λ a, TRANS (mult_commute a _1) (mult_1 a));

injective typeclass symbol cancel_semigroup_add_class : Set → TYPE;
constant symbol mk_cancel_semigroup_add [A : Set] [B : semigroup_add_class A]:
  Prf (`∀ a, `∀ b, `∀ c, a + b = a + c ⇒ b = c) → Prf (`∀ a, `∀ b, `∀ c, b + a = c + a ⇒ b = c) → cancel_semigroup_add_class A;

instance symbol semigroup_add_of_cancel_semigroup_add [A : Set] :
  cancel_semigroup_add_class A → semigroup_add_class A;
rule semigroup_add_of_cancel_semigroup_add (@mk_cancel_semigroup_add _ $prf _ _) ↪ $prf;

symbol add_left_imp_eq [A] [B : cancel_semigroup_add_class A] :
  Prf (`∀ a, `∀ b, `∀ c, a + b = a + c ⇒ b = c);

symbol add_right_imp_eq [A] [B : cancel_semigroup_add_class A] :
  Prf (`∀ a, `∀ b, `∀ c, b + a = c + a ⇒ b = c);

injective typeclass symbol cancel_ab_semigroup_add_class : Set → TYPE;
constant symbol mk_cancel_ab_semigroup_add [A : Set] [B : ab_semigroup_add_class A] [C : minus_class A]:
  Prf (`∀ a, `∀ b, (a + b) - a = b) → Prf (`∀ a, `∀ b, `∀ c, a - b - c = a - (b + c)) → cancel_ab_semigroup_add_class A;

instance symbol ab_semigroup_add_of_cancel_ab_semigroup_add [A : Set] :
  cancel_ab_semigroup_add_class A → ab_semigroup_add_class A;
rule ab_semigroup_add_of_cancel_ab_semigroup_add (@mk_cancel_ab_semigroup_add _ $prf _ _ _) ↪ $prf;

instance symbol minus_of_cancel_ab_semigroup_add [A : Set] :
  cancel_ab_semigroup_add_class A → minus_class A;
rule minus_of_cancel_ab_semigroup_add (@mk_cancel_ab_semigroup_add _ _ $prf _ _) ↪ $prf;

symbol add_diff_cancel_left' [A] [B : cancel_ab_semigroup_add_class A] :
  Prf (`∀ a, `∀ b, (a + b) - a = b);

symbol diff_diff_add [A] [B : cancel_ab_semigroup_add_class A] :
  Prf (`∀ a, `∀ b, `∀ c, a - b - c = a - (b + c));

opaque symbol add_diff_cancel_right' [A] [B : cancel_ab_semigroup_add_class A]: 
 Prf (`∀ a, `∀ b, (a + b) - b = a) ≔ begin
  assume A ? a b;
  rewrite add_commute;
  refine (add_diff_cancel_left' b a);
end;

instance symbol cancel_semigroup_add_of_cancel_ab_semigroup_add [A] :
  cancel_ab_semigroup_add_class A → cancel_semigroup_add_class A ≔ begin
  assume A ?; apply mk_cancel_semigroup_add
  {
    assume a b c eqabac; rewrite left (add_diff_cancel_left' a b);
    rewrite left (add_diff_cancel_left' a c);
    rewrite eqabac; reflexivity;
  }
  {
    assume a b c eqabac; rewrite left (add_diff_cancel_right' b a);
    rewrite left (add_diff_cancel_right' c a);
    rewrite eqabac; reflexivity;
  }
end;

injective typeclass symbol group_add_class : Set → TYPE;
constant symbol mk_group_add [A] [B : minus_class A] [C : uminus_class A] [D : monoid_add_class A] :
  Prf (`∀ a, — a + a = _0) → Prf (`∀ a, `∀ b, a + — b = a - b) → group_add_class A;

instance symbol minus_of_group_add [A] : group_add_class A → minus_class A;
rule minus_of_group_add (@mk_group_add _ $prf _ _ _ _) ↪ $prf;
instance symbol uminus_of_group_add [A] : group_add_class A → uminus_class A;
rule uminus_of_group_add (@mk_group_add _ _ $prf _ _ _) ↪ $prf;
instance symbol monoid_add_of_group_add [A] : group_add_class A → monoid_add_class A;
rule monoid_add_of_group_add (@mk_group_add _ _ _ $prf _ _) ↪ $prf;

symbol left_minus [A] [B : group_add_class A] :
  Prf (`∀ a, — a + a = _0);

symbol add_uminus_conv_diff [A] [B : group_add_class A] :
  Prf (`∀ a, `∀ b, a + — b = a - b);

opaque symbol diff_conv_add_uminus [A] [B : group_add_class A] :
  Prf (`∀ a, `∀ b, a - b = a + — b) ≔ begin
  assume A ? a b; symmetry; refine (add_uminus_conv_diff a b);
end;

opaque symbol minus_unique [A] [B : group_add_class A] :
  Prf (`∀ a, `∀ b, a + b = _0 ⇒ — a = b) ≔ begin
    assume A ? a b sum0; rewrite left (add_0_right (— a));
    rewrite left sum0; rewrite left add_assoc;
    rewrite left_minus; apply add_0_left;
end;

opaque symbol minus_zero [A] [B : group_add_class A] :
  Prf (— _0 = _0) ≔ begin
  assume A ?; rewrite left (add_0_right (— _0));
  refine (left_minus _0);
end;

opaque symbol minus_minus [A] [B : group_add_class A] :
  Prf (`∀ a, — — a = a) ≔ begin
  assume A ? a; apply (minus_unique (— a));
  refine (left_minus a);
end;

opaque symbol right_minus [A] [B : group_add_class A] :
  Prf (`∀ a, a + — a = _0) ≔ begin
  assume A ? a; rewrite left .[X in X + _](minus_minus a);
  refine (left_minus (— a));
end;

opaque symbol diff_self [A] [B : group_add_class A] :
  Prf (`∀ a, a - a = _0) ≔ begin
  assume A ? a; rewrite diff_conv_add_uminus;
  refine (right_minus a);    
end;

opaque instance symbol cancel_semigroup_add_of_group_add [A] :
  group_add_class A → cancel_semigroup_add_class A ≔ begin
    assume A ?; apply mk_cancel_semigroup_add {
      assume a b c eqabac; rewrite left (add_0_left b);
      rewrite left (add_0_left c); rewrite left (left_minus a);
      rewrite add_assoc; rewrite add_assoc;
      rewrite eqabac; reflexivity;
    } {
      assume a b c eqbaca; rewrite left (add_0_right b);
      rewrite left (add_0_right c); rewrite left (right_minus a);
      rewrite left add_assoc; rewrite left add_assoc;
      rewrite eqbaca; reflexivity;
    }; 
end;

opaque symbol minus_add_cancel [A : Set] [B : group_add_class A] a b :
  Prf (— a + (a + b) = b) ≔ begin
  assume A ? a b; rewrite left add_assoc; rewrite left_minus;
  rewrite add_0_left; reflexivity;
end;

opaque symbol add_minus_cancel [A] [_ : group_add_class A] a b :
  Prf (a + (— a + b) = b) ≔ begin
  assume A ? a b ; rewrite left add_assoc; rewrite right_minus;
  rewrite add_0_left; reflexivity;
end;

opaque symbol diff_add_cancel [A] [_ : group_add_class A] a b :
  Prf (a - b + b = a) ≔ begin
  assume A ? a b; rewrite diff_conv_add_uminus; rewrite add_assoc;
  rewrite left_minus; apply add_0_right;
end;

opaque symbol add_diff_cancel [A] [_: group_add_class A] a b :
  Prf (a + b - b = a) ≔ begin
  assume A ? a b; rewrite diff_conv_add_uminus; rewrite add_assoc;
  rewrite right_minus; apply add_0_right;
end;

opaque symbol minus_add [A] [_ : group_add_class A] a b :
  Prf (— (a + b) = — b + — a) ≔ begin
  assume A ? a b; apply (minus_unique (a + b));
  rewrite add_assoc; rewrite left (add_assoc b);
  rewrite right_minus; rewrite add_0_left;
  refine (right_minus a);
end;

symbol ⊥ₑ : Prf ⊥ → Π p, Prf p;
symbol ¬_def : Prf ((¬) = (λ p, p ⇒ ⊥));

instance symbol boolF2_zero ≔ mk_zero ⊥;
instance symbol boolF2_uminus ≔ mk_uminus (λ (b : El bool), b);
instance symbol boolF2_plus ≔ mk_plus (λ b b', (b ∧ ¬ b') ∨ (¬ b ∧ b'));
symbol deduce_minus [A] [_ : plus_class A] [_ : uminus_class A] : minus_class A
  ≔ mk_minus (λ (x y : El A), x + — y);
instance symbol boolF2_minus : minus_class bool ≔ deduce_minus;

opaque symbol ∧ᵢ_alt [p q] : Prf p → Prf q → Prf (p ∧ q) ≔ λ Hp Hq, ∧ᵢ Hp Hq;
opaque symbol ∨ᵢ₂_alt [q : El bool] : Prf q → Π p : El bool, Prf (p ∨ q) ≔
  λ Hq p, ∨ᵢ₂ p Hq;
//provable of course
symbol EM p : Prf (p ∨ ¬ p);

opaque symbol boolF2_add_assoc (a b c : El bool) :
  Prf (((a + b) + c) = (a + (b + c))) ≔ begin
  assume b b' b''; apply prop_ext {
    assume bigsumtrue; apply (∨ₑ bigsumtrue) {
      change (Prf _); rewrite ¬_def; simplify rule off;
      assume bigconjtrue ; apply (∨ₑ (∧ₑ₁ bigconjtrue)) {
        change (Prf _); rewrite ¬_def; simplify rule off;
        assume smallconjtrue; apply ∨ᵢ₁; apply (∧ᵢ_alt) {
          refine (∧ₑ₁ smallconjtrue)
        } {
          rewrite ¬_def; simplify rule off; assume smallsumtrue;
          apply (∨ₑ smallsumtrue) {
            assume contra; apply (∧ₑ₂ smallconjtrue _);
            refine (∧ₑ₁ contra);
          } {
            assume contra; apply (∧ₑ₂ bigconjtrue _);
            refine (∧ₑ₂ contra);
          };
        }
      } {
        change (Prf _); rewrite ¬_def; simplify rule off;
        assume smallconjtrue; apply ∨ᵢ₂_alt; apply (∧ᵢ_alt) {
          rewrite ¬_def; refine (∧ₑ₁ smallconjtrue)
        } {
          apply ∨ᵢ₁; apply ∧ᵢ_alt {
            refine (∧ₑ₂ smallconjtrue);
          } {
            rewrite ¬_def; refine (∧ₑ₂ bigconjtrue)
          };
        }
      }
    } {
      change (Prf (_ ⇒ _)); rewrite ¬_def; simplify rule off;
      assume bigconjtrue ; apply (∨ₑ (EM b)) {
        assume Hb; apply ∨ᵢ₁; apply (∧ᵢ_alt Hb);
        rewrite ¬_def; assume smallsumtrue; 
        apply (∨ₑ smallsumtrue) {
          change (Prf _); rewrite ¬_def; simplify rule off;
          assume smallconjtrue; apply (∧ₑ₂ smallconjtrue _) ;
          refine (∧ₑ₂ bigconjtrue)
        } {
          assume smallconjtrue; apply (∧ₑ₁ bigconjtrue _);
          apply ∨ᵢ₁; refine (∧ᵢ Hb (∧ₑ₁ smallconjtrue))
        };
      } {
        assume Hnb; apply ∨ᵢ₂_alt; apply (∧ᵢ_alt Hnb);
        apply ∨ᵢ₂_alt; apply (∧ᵢ_alt _ (∧ₑ₂ bigconjtrue));
        rewrite ¬_def; assume Hb'; apply (∧ₑ₁ bigconjtrue _);
        refine (∨ᵢ₂ _ (∧ᵢ Hnb Hb'));
      };
    };
  } {
    assume bigsumtrue; apply (∨ₑ bigsumtrue) {
      change (Prf _); rewrite ¬_def; simplify rule off;
      assume bigconjtrue ; apply (∨ₑ (EM b'')) {
        assume Hb''; apply ∨ᵢ₂_alt; apply (∧ᵢ_alt _ Hb'');
        rewrite ¬_def; assume smallsumtrue; 
        apply (∨ₑ smallsumtrue) {
          assume smallconjtrue; apply (∧ₑ₂ bigconjtrue _);
          apply ∨ᵢ₂_alt; refine (∧ᵢ (∧ₑ₂ smallconjtrue) Hb'')
        } {
          change (Prf _); rewrite ¬_def; simplify rule off;
          assume smallconjtrue; apply (∧ₑ₁ smallconjtrue _) ;
          refine (∧ₑ₁ bigconjtrue)
        };
      } {
        assume Hnb''; apply ∨ᵢ₁; apply (∧ᵢ_alt _ Hnb'');
        apply ∨ᵢ₁; apply (∧ᵢ_alt (∧ₑ₁ bigconjtrue));
        rewrite ¬_def; assume Hb'; apply (∧ₑ₂ bigconjtrue _);
        refine (∨ᵢ₁ (∧ᵢ Hb' Hnb'') _);
      };
    } {
      change (Prf _); rewrite ¬_def; simplify rule off;  
      assume bigconjtrue ; apply (∨ₑ (∧ₑ₂ bigconjtrue)) {
        assume smallconjtrue; apply ∨ᵢ₁;
        apply (∧ᵢ_alt _ (∧ₑ₂ smallconjtrue));
        simplify; rewrite ¬_def;
        refine (∨ᵢ₂ _ (∧ᵢ (∧ₑ₁ bigconjtrue) (∧ₑ₁ smallconjtrue)))
      } {
        change (Prf _); rewrite ¬_def; simplify rule off;  
        assume smallconjtrue; apply ∨ᵢ₂_alt;
        apply (∧ᵢ_alt _ (∧ₑ₂ smallconjtrue)); rewrite ¬_def;
        assume smallsumtrue;  apply (∨ₑ smallsumtrue) {
          refine (λ contra, ∧ₑ₁ bigconjtrue (∧ₑ₁ contra))
        } {
          refine (λ contra, ∧ₑ₁ smallconjtrue (∧ₑ₂ contra))
        };
      }
    };
  };
end;

instance symbol boolF2_semigroup_add ≔ mk_semigroup_add boolF2_add_assoc;

opaque symbol ¬⊥ : Prf ((¬ ⊥) = ⊤) ≔ begin
  apply (prop_ext (λ _, ⊤ᵢ));
  assume ?; rewrite ¬_def; refine (λ H⊥, H⊥);
end;

opaque symbol ∧_⊤_left p : Prf ((⊤ ∧ p) = p) ≔ prop_ext ∧ₑ₂ (λ Hp, ∧ᵢ ⊤ᵢ Hp);

opaque symbol boolF2_add_0_left (a : El bool) : Prf (_0 + a = a) ≔ begin
  assume a; apply prop_ext {
    assume 0+a; apply (∨ₑ 0+a) {
      assume contra; apply ⊥ₑ; refine (∧ₑ₁ contra) 
    } {
      assume res; refine (∧ₑ₂ res)
    };
  } {
    assume Ha; apply ∨ᵢ₂_alt; simplify; rewrite ¬⊥;
    rewrite ∧_⊤_left; refine Ha
  };
end;

opaque symbol boolF2_add_comm (a b : El bool) : Prf (a + b = b + a) ≔ begin
  assume a b; apply prop_ext {
    assume a+b; apply (∨ₑ a+b) {
      assume a∧¬b; apply ∨ᵢ₂_alt;
      refine (∧ᵢ (∧ₑ₂ a∧¬b) (∧ₑ₁ a∧¬b))
    } {
      assume ¬a∧b; apply ∨ᵢ₁;
      refine (∧ᵢ (∧ₑ₂ ¬a∧b) (∧ₑ₁ ¬a∧b))
    }
  } {
    assume a+b; apply (∨ₑ a+b) {
      assume a∧¬b; apply ∨ᵢ₂_alt;
      refine (∧ᵢ (∧ₑ₂ a∧¬b) (∧ₑ₁ a∧¬b))
    } {
      assume ¬a∧b; apply ∨ᵢ₁;
      refine (∧ᵢ (∧ₑ₂ ¬a∧b) (∧ₑ₁ ¬a∧b))
    }
  }
end;

instance symbol boolF2_monoid_add : monoid_add_class bool ≔ begin
  apply mk_monoid_add boolF2_add_0_left;
  assume a; rewrite boolF2_add_comm; apply boolF2_add_0_left;
end;

opaque symbol boolF2_*2=0 (b : El bool) : Prf (b + b = ⊥) ≔ begin
  assume b; apply (prop_ext _ (λ H⊥, ⊥ₑ H⊥ _)); assume b+b;
  apply (∨ₑ b+b) {
    change (Prf _); rewrite ¬_def; refine (λ c, ∧ₑ₂ c (∧ₑ₁ c))
  } {
    change (Prf _); rewrite ¬_def; refine (λ c, ∧ₑ₁ c (∧ₑ₂ c))
  }
end;

instance symbol boolF2_group_add : group_add_class bool ≔ begin
  apply (mk_group_add boolF2_*2=0); reflexivity;
end;

symbol test (a b : El bool) : Prf (a + b + b = a) ≔ begin
  assume a b; apply add_diff_cancel;
end;