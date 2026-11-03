// n-ary functions and relations

/*
following "Generic Level Polymorphic N-ary Functions" by Guillaume
Allais (TyDe 2019). */

require open tests.OK.HOL tests.OK.Nat;

// vectors of type codes
inductive VSet : ℕ → TYPE ≔
| ◃ : VSet 0 // \smalltriangleleft
| ▹ : Set → Π [n], VSet n → VSet (n +1); // \smalltriangleright

notation ▹ infix right 10;

// tail
symbol tl [n] : VSet (n +1) → VSet n;
rule tl (_ ▹ $ts) ↪ $ts;

// constant vector
injective symbol vcst n (t : Set) : VSet n;
rule vcst 0 _ ↪ ◃
with vcst ($n +1) $t ↪ $t ▹ vcst $n $t;

// type code of n-ary functions: fun (a₁ ▹ … ▹ aₙ ▹ ◃) b ≡ a₁ ⤳ … ⤳ aₙ ⤳ b
symbol fun [n] : VSet n → Set → Set;
rule fun ◃ $b ↪ $b
with fun ($t ▹ $ts) $b ↪ $t ⤳ fun $ts $b;

// fun is not injective, however (fun d) and (fun _ b) are both injective
// we can therefore safely add the following unification rules:
unif_rule fun $x $y ≡ fun $x $y' ↪ [$y ≡ $y'];
unif_rule fun $x $y ≡ fun $x' $y ↪ [$x ≡ $x'];
unif_rule fun $x $y ≡ $y ↪ [$x ≡ ◃];

// type of n-ary functions
symbol Fun [n] (dom : VSet n) cod ≔ τ (fun dom cod);

// type of n-ary endofunctions
injective symbol Endo n a ≔ Fun (vcst n a) a;

// lift (a₁ ▹ … ▹ aₙ ▹ ◃) p f x₁ … xₙ ≡ p (f x₁ … xₙ) 
symbol lift [a b n] (d: VSet n): (τ a → τ b) → Fun d a → Fun d b;
rule lift ◃ $op $f ↪ $op $f
with lift (_ ▹ $ts) $op $f ↪ λ x, lift $ts $op ($f x);

// comp (a₁ ▹ … ▹ aₙ ▹ ◃) g f x₁ … xₙ ≡ g x₁ … xₙ ∘ f
symbol comp [n] (d: VSet n) [j b] (g: Fun d (j ⤳ b)) [i] (f: τ i → τ j)
  : Fun d (i ⤳ b) ≔ lift d (λ h:_ → τ b, h ∘ f) g;

// lift2 (a₁ ▹ … ▹ aₙ ▹ ◃) p f g x₁ … xₙ ≡ p (f x₁ … xₙ) (g x₁ … xₙ)
symbol lift2 [a b c n] (d: VSet n) :
  (τ a → τ b → τ c) → Fun d a → Fun d b → Fun d c;
rule lift2 ◃ $op $f $g ↪ $op $f $g
with lift2 (_ ▹ $ts) $op $f $g ↪ λ x, lift2 $ts $op ($f x) ($g x);

// cong (a₁ ▹ … ▹ aₙ ▹ ◃) r f g ≡
// `∀ x₁,`∀ y₁, x₁ = y₁ ⇒ … ⇒ `∀ xₙ,`∀ yₙ, xₙ = yₙ ⇒ f x₁ … xₙ = g y₁ … yₙ
symbol cong [n] (ts: VSet n) [r] (f g: Fun ts r): Prop;
rule cong ◃ $f $g ↪ $f = $g
with cong (_ ▹ $ts) $f $g ↪ `∀ x,`∀ y, x = y ⇒ cong $ts ($f x) ($g y);

opaque symbol refl_cong [n] (ts: VSet n) [r] (f: Fun ts r): π(cong ts f f) ≔
begin
  have aux: Π r n (ts: VSet n) (f: Fun ts r), π(cong ts f f) {
    assume r n; refine ind_VSet (λ n ts, `∀ f, cong ts [r] f f) _ _ n
    { reflexivity }
    { assume t m ts ih f x y xy; rewrite xy; refine ih (f y) }
  };
  assume n ts r; refine aux r n ts
end;

require open tests.OK.Impred;

// subst (a₁ ▹ … ▹ aₙ ▹ ◃) f g ≡
// `∀x₁:τa₁,`∀y₁, x₁ = y₁ ⇒ … ⇒ `∀xₙ:τaₙ,`∀yₙ, xₙ = yₙ ⇒ f x₁ … xₙ ⇒ g y₁ … yₙ
symbol subst [n] (ts: VSet n) (f g: Fun ts o): Prop;
rule subst ◃ $f $g ↪ $f ⇒ $g
with subst (_ ▹ $ts) $f $g ↪ `∀ x,`∀ y, x = y ⇒ subst $ts ($f x) ($g y);

opaque symbol refl_subst [n] (ts: VSet n) (p: Fun ts o): π(subst ts p p) ≔
begin
  assume n; refine ind_VSet (λ n ts, `∀ p, subst ts p p) _ _ n
  { assume p h; refine h }
  { assume t m ts ih p x y xy; rewrite xy; refine ih (p y) }
end;

// lifted connectors
symbol ∧ₙ [n] [d: VSet n] ≔ lift2 d (∧);
symbol ∨ₙ [n] [d: VSet n] ≔ lift2 d (∨);
symbol ⇒ₙ [n] [d: VSet n] ≔ lift2 d (⇒);

// quantₙ Q (a₁ ▹ … ▹ aₙ ▹ ◃) p ≡ `Q x₁, …, `Q xₙ, p x₁ … xₙ
symbol quantₙ (q: Π a, (τ a → Prop) → Prop) [n] (ts: VSet n): Fun ts o → Prop;
rule quantₙ _ ◃ $p ↪ $p
with quantₙ $q ($t ▹ $ts) $p ↪ $q $t (λ x, quantₙ $q $ts ($p x));

symbol ∀ₙ [n] ≔ @quantₙ @∀ n;
symbol ∃ₙ [n] ≔ @quantₙ @∃ n;

// tests

private symbol f1 : Endo 4 o;

private opaque symbol ex_cong a b c d x y w z :
  π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (f1 a b c d = f1 x y w z) ≔
begin
  assume a b c d x y w z heq1 heq2 heq3 heq4;
  refine refl_cong (o ▹ o ▹ o ▹ o ▹ ◃) f1 _ _ heq1 _ _ heq2 _ _ heq3 _ _ heq4
end;

private opaque symbol ex_cong_param a b c d x y w z
  (g : Fun (o ▹ o ▹ o ▹ o ▹ ◃) o) :
  π (a = x) → π (b = y) → π (c = w) → π (d = z) → π (g a b c d = g x y w z) ≔
begin
  assume a b c d x y w z g heq1 heq2 heq3 heq4;
  refine refl_cong (o ▹ o ▹ o ▹ o ▹ ◃) g _ _ heq1 _ _ heq2 _ _ heq3 _ _ heq4
end;

private opaque symbol ex_cong_add (a b x y : ℕ) :
  π (a = x) → π (b = y) → π (a + b = x + y) ≔
begin
  assume a b x y h1 h2;
  refine refl_cong (nat ▹ nat ▹ ◃) (+) _ _ h1 _ _ h2
end;

assert x y ⊢ let u ≔ comp (nat ▹ ◃) (+) (+1) in u x y ≡ x + (y +1);

private opaque symbol testSubst (p: Fun (nat ▹ nat ▹ ◃) o) a b x y:
  π (a = x) → π (b = y) → π (p a b) → π (p x y) ≔
begin
  assume p a b x y ax by;
  refine refl_subst (nat ▹ nat ▹ ◃) p _ _ ax _ _ by
end;
