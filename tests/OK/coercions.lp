// Tests on coercions. We define several mathematical structures forming a
// hierarchy and work on coercions to and from them.

//
// Encoding
//
constant symbol Set: TYPE;
symbol El (_: Set): TYPE;

symbol -> (_ _: Set): Set;
notation -> infix right 6;
rule El ($x -> $y) ↪ Π _ : El $x, El $y;

constant symbol Prop: TYPE;
symbol Prf : Prop → TYPE;

symbol => : Prop → Prop → Prop;
notation => infix right 6;
rule Prf ($P => $Q) ↪ Prf $P → Prf $Q;

symbol all : Π x : Set, ((El x) → Prop) → Prop;
rule Prf (all $x $p) ↪ Π (z: El $x), Prf ($p z);

symbol ex : Π x : Set, ((El x) → Prop) → Prop;
symbol eq (supp: Set): El supp → El supp → Prop;

//
// Magmas. A magma (G, *) is a support G and a binary operation *.
//

constant symbol Magma: TYPE;
constant symbol magma (supp: Set): El (supp -> supp -> supp) → Magma;

// Projections
symbol mg-support (_: Magma): Set;
rule mg-support (magma $supp _) ↪ $supp;
symbol mg-binop (m: Magma): let S : Set ≔ mg-support m in El (S -> S -> S);
rule mg-binop (magma _ $binop) ↪ $binop;

// Coercion from a magma to its support, so that we can write
// "forall magma M, forall e in M" instead of "forall magma M, forall e in the
// support of M"
coerce_rule coerce Magma Set $magma ↪ mg-support $magma;

constant symbol Z : Set;
constant symbol + : El (Z -> Z -> Z);
symbol mZ : Magma ≔ magma Z +;

//
// Semigroups
//

// A semigroup is a magma (S, *) where * is associative.
constant symbol Semigroup: TYPE;
constant symbol semigroup
  (supp: Set)
  (op: El (supp -> supp -> supp))
  (_: Prf (all supp (λ a: El supp,
           all supp (λ b: El supp,
	   all supp (λ c: El supp,
	   eq supp
	      (op (op a b) c)
	      (op a (op b c))))))) // Associativity proof
: Semigroup;

// A projection
symbol sg-support (_: Semigroup): Set;
rule sg-support (semigroup $supp _ _) ↪ $supp;

// Coerce from semigroups to their support
coerce_rule coerce Semigroup Set $grp ↪ sg-support $grp;

// Create the semigroup (Z, +, zero)
// Associativity of +
symbol addrA:
  Prf (all Z (λ a: El Z,
       all Z (λ b: El Z,
       all Z (λ c : El Z,
       eq Z (+ (+ a b) c)
            (+ a (+ b c))))));

symbol sZ : Semigroup ≔ semigroup Z + addrA;

assert ⊢ sZ: Set; // Coercion form semigroups to supports

// Coercions on functions: we add this standard coercion rule to
// implement covariance on the codomain.
coerce_rule coerce (Π x: $A, $B.[x]) (Π x: $A, $C.[x]) (λ x : $A, $e.[x]) ↪
  λ x: $A, coerce $B.[x] $C.[x] $e.[x];

// The body of the function is coerced
assert ⊢ λ _ : El (Z -> Z -> Z), sZ: El (Z -> Z -> Z) → Set;

// Coercions may require proof obligations: a magma can be coerced to a
// semigroup if we can prove that the binary operation is associative.
// We define a coercion that leaves a hole for the proof.
coerce_rule coerce Magma Semigroup $magma ↪
  semigroup (mg-support $magma) (mg-binop $magma) _;

// This symbol requires to prove that the magma M is a semigroup thrice
constant symbol mop (M: Magma):
  El (sg-support M -> sg-support M -> sg-support M)
begin
  admit;
  admit;
  admit; // hence we have three proof obligations.
end;

assert ⊢ mZ : Semigroup;
