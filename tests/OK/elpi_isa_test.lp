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

/* HOL-Light derived connectives */
constant symbol ∃₁ [A] : El (fun (fun A bool) bool); notation ∃₁ quantifier;
constant symbol ¬ : El (fun bool bool); notation ¬ prefix 30;
constant symbol ⊥ : El bool;
constant symbol ∨ : El (fun bool (fun bool bool)); notation ∨ infix 25;
constant symbol ∃ [A] : El (fun (fun A bool) bool); notation ∃ quantifier;
constant symbol ∀ [A] : El (fun (fun A bool) bool); notation ∀ quantifier;
constant symbol ⇒ : El (fun bool (fun bool bool)); notation ⇒ infix 15;
constant symbol ∧ : El (fun bool (fun bool bool)); notation ∧ infix 20;
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
symbol + [A : Set] [B : plus_class A] : El (fun A (fun A A)); notation + infix 65;
rule @+ _ (mk_plus $add) ↪ $add;

injective typeclass symbol minus_class : Set → TYPE;
constant symbol mk_minus [A : Set] : El (fun A (fun A A)) → minus_class A;
symbol - [A : Set] [B : minus_class A] : El (fun A (fun A A)); notation - infix 65;
rule @- _ (mk_minus $sub) ↪ $sub;

injective typeclass symbol uminus_class : Set → TYPE;
constant symbol mk_uminus [A : Set] : El (fun A A) → uminus_class A;
symbol u- [A : Set] [B : uminus_class A] : El (fun A A); notation u- prefix 80;
rule @u- _ (mk_uminus $opp) ↪ $opp;

injective typeclass symbol times_class : Set → TYPE;
constant symbol mk_times [A : Set] : El (fun A (fun A A)) → times_class A;
symbol * [A : Set] [B : times_class A] : El (fun A (fun A A)); notation * infix 70;
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

//TODO: report later: adding an extra underscore after mk_comm_monoid_add triggers the wrong error message.
rule @ab_semigroup_add_of_comm_monoid_add _ (@mk_comm_monoid_add _ _ $prf _) ↪ $prf;

symbol add_0 [A : Set] [B : comm_monoid_add_class A] : Prf (`∀ a, _0 + a = a);

instance symbol monoid_add_of_comm_monoid_add [A : Set] [B : comm_monoid_add_class A] : monoid_add_class A ≔
  mk_monoid_add add_0 (λ a, TRANS (add_commute a _0) (add_0 a));
//symbol zero_reorient [A : Set] [B : monoid_add_class A] : Prf (`∀ x, (0 = x) = (x = 0))