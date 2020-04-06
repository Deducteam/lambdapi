require open tests.preuves_Ledein.notation

// Induction principle
symbol nat_ind P : π (P 0) ⇒ (∀x, π (P x) ⇒ π (P (S x))) ⇒ ∀x, π (P x)
rule nat_ind _  &u _  O      → &u
 and nat_ind &p &u &v (S &n) → &v &n (nat_ind &p &u &v &n)

// Addition
symbol add : N ⇒ N ⇒ N
set infix left 6 "+" ≔ add
                       
assert λx y z,x+y+z ≡ λx y z,(x+y)+z // check that x+y=z is parsed correctly

rule   0  + &y → &y            // les autres règles en découlent
 and S &x + &y → S (&x + &y)

// Addition is commutative
theorem add0r x : π (eq {nat} (x + 0) x)
proof
  refine nat_ind _ _ _
  // case x = 0
  reflexivity
  // case x = s x'
  assume x' h
  simpl
  rewrite h
  reflexivity
qed

rule &x + 0 → &x

theorem addsr x y : π (x + S y = S (x + y))
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  assume x' h y
  simpl
  rewrite h
  reflexivity
qed

rule &x + S &y → S (&x + &y)

theorem add_com x y : π (x+y = y+x)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  simpl
  assume x' h y
  rewrite h
  reflexivity
qed

// Addition is associative
theorem add_assoc x y z : π ((x+y)+z = x+(y+z))
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y z
  reflexivity
  // case x = s x'
  assume x' h y z
  simpl
  rewrite h
  reflexivity
qed

rule (&x + &y) + &z → &x + (&y + &z)

// Multiplication
symbol mul : N ⇒ N ⇒ N
set infix left 7 "×" ≔ mul
                       
assert λx y z,x+y×z ≡ λx y z,x+(y×z) // check that x+y×z is parsed correctly

rule       0 × _  → 0          // les autres règles en découlent
 and S &x × &y → &y + &x × &y

// Multiplication is commutative
theorem mul0r x : π (x × 0 = 0)
proof
  refine nat_ind _ _ _
  // case x = 0
  reflexivity
  // case x = s x'
  assume x' h
  apply h
qed

rule _ × 0 → 0

theorem mulsr x y : π (x × S y = x × y + x)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  assume x' h y
  simpl
  rewrite h
  reflexivity
qed

rule &x × S &y → &x + &x × &y

theorem mul_com x y : π (x × y = y × x)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y
  reflexivity
  // case x = s x'
  assume x' h y
  simpl
  rewrite h
  reflexivity
qed

// Multiplication distributes over addition
theorem mul_addl x y z : π ((x+y)×z = x×z+y×z)
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y z
  reflexivity
  // case x = s x'
  assume x' h y z
  simpl
  rewrite h
  reflexivity
qed

rule (&x + &y) × &z → &x × &z + &y × &z

theorem mul_addr x y z : π (z×(x+y) = z×x+z×y)
proof
  assume x y z
  rewrite mul_com
  rewrite mul_addl
  rewrite mul_com
  rewrite [y×_]mul_com
  reflexivity
qed

rule &z × (&x + &y) → &z × &x + &z × &y

// Multiplication is associative
theorem mul_assoc x y z : π ((x × y) × z = x × (y × z))
proof
  refine nat_ind _ _ _
  // case x = 0
  assume y z
  reflexivity
  // case x = s x'
  assume x' h y z
  simpl
  rewrite h
  reflexivity
qed

rule (&x × &y) × &z → &x × (&y × &z)

// Doubling function.
definition double n ≔ mul n 2
