// test generation of inductive principle for a strictly-positive type

constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "P" ≔ π;

/* Sorts */
symbol Sort : TYPE;
constant symbol s0 : Sort;
constant symbol snext : Sort → Sort;

symbol smax : Sort → Sort → Sort;
rule smax s0 $n ↪ $n
with smax $n s0 ↪ $n
with smax (snext $n) (snext $m) ↪ snext (smax $n $m);

/* Terms */
/* HOAS style, in order to avoid having to bother with De Brujin indices and α
renaming. */
symbol Term : TYPE;
// Dependent λ-calculus
constant symbol tabs
              : Term // Type of the argument
              → (Term → Term) // Type of result
              → (Term → Term) // Body of the abstraction
              → Term;
constant symbol tapp
              : Term // Type of the argument of the function
              → (Term → Term) // Type of the result
              → Term // Function
              → Term // Argument
              → Term;
constant symbol tfun
              : Term // Type of the argument
              → (Term → Term) // Type of the result
              → Term;
constant symbol tsort : Sort → Term;
// Dependent pairs
constant symbol tpair
              : Term // Type of the first element
              → (Term → Term) // Type of the second element
              → Term // First element
              → Term // Second element
              → Term;
constant symbol π1
              : Term // First type of the pair
              → (Term → Term) // Second type of the pair
              → Term // The pair
              → Term;
constant symbol π2
              : Term // First type of the pair
              → (Term → Term) // Second type of the pair
              → Term // The pair
              → Term;
constant symbol tsum
              : Term // Type of the first element
              → (Term → Term) // Type of the second element
              → Term;
// Propositional equality
constant symbol trefl
              : Term // Type
              → Term // Term
              → Term;
constant symbol J
              : Term // Type of the term to rewrite A
              → Term // Term to rewrite u
              → (Term → Term → Term) // Proposition depending on the term and the equality aka P
              → Term // Proof of P(u, refl A u)
              → Term // Term to rewrite u by
              → Term // Proof of equality between the terms to rewrite
              → Term;
constant symbol teq
              : Term // Type of the equality
              → Term → Term → Term;
// Axioms
constant symbol funext
              : Term // Type of the argument
              → (Term → Term) // Type of the result
              → Term // First function
              → Term // Second function
              → Term // Proof of equality point by point
              → Term;
constant symbol uip
              : Term // Type
              → Term → Term // The two terms
              → Term → Term // The two equalities
              → Term;

constant symbol Var : TYPE;
constant symbol VAR : Var → Term → Term; // Represents a bound variable of type its argument

/* Typing derivation */
inductive der : Term → Term → TYPE ≔

// Types
| der_sort : Π(s : Sort), der (tsort s) (tsort (snext s))
| der_prod :
  Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
  der A (tsort s) → der (B A) (tsort s') → der (tfun A B) (tsort (smax s s'))
| der_sigma :
  Π(s s' : Sort), Π(A : Term), Π(B : Term → Term),
  der A (tsort s) → der (B A) (tsort s') → der (tsum A B) (tsort (smax s s'))
| der_prop_type_eq :
  Π(s : Sort), Π(A u v : Term),
  der A (tsort s) → der u A → der v A → der (teq A u v) (tsort s)

// Structural rules
| der_var : Π(A : Term), Π(v : Var), der (VAR v A) A
| der_type_conv :
  Π (u A B : Term), Π(s : Sort),
  der u A → der_eq A B (tsort s) → der u B

// λ-calculus terms
| der_abs :
  Π(s s' : Sort), Π(A : Term), Π(t B : Term → Term),
  der A (tsort s) → (Π(v : Var), der (B (VAR v A)) (tsort s')) → (Π(v : Var), der (t (VAR v A)) (B (VAR v A)))
  → der (tabs A B t) (tfun A B)
| der_app :
  Π(s s' : Sort), Π(A t u : Term), Π(B : Term → Term),
  der A (tsort s) → (Π(v : Var), der (B (VAR v A)) (tsort s'))
  → der t (tfun A B) → der u A → der (tapp A B t u) (B u)
| der_pair :
  Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
  der A (tsort s) → der u A → (Π(v : Var), der (B (VAR v A)) (tsort s')) → der v (B u)
  → der (tpair A B u v) (tsum A B)
| der_π1 :
  Π(p A : Term), Π(B : Term → Term),
  der p (tsum A B) → der (π1 A B p) A
| der_π2 :
  Π(p A : Term), Π(B : Term → Term),
  der p (tsum A B) → der (π2 A B p) (B (π1 A B p))
// Equality terms
| der_refl :
  Π(s : Sort), Π(u A : Term),
  der A (tsort s) → der u A → der (trefl A u) (teq A u u)
| der_uip :
  Π(e1 e2 u v A : Term),
  der e1 (teq A u v) → der e2 (teq A u v) → der (uip A u v e1 e2) (teq (teq A u v) e1 e2)
| der_J :
  Π(s s' : Sort), Π(A u v p w : Term), Π(P : Term → Term → Term),
  der A (tsort s) → der u A → der v A
  → (Π(v1 v2 : Var), der (P (VAR v1 A) (VAR v2 (teq A u (VAR v1 A)))) (tsort s'))
  → der p (teq A u v) → der w (P u (trefl A u))
  → der (J A u P w v p) (P v p)
| der_funext :
  Π(f g A e : Term), Π(B : Term → Term),
  der f (tfun A B) → der g (tfun A B)
  → der e (tfun A (λ u, teq (B u) (tapp A B f u) (tapp A B g u)))
  → der (funext A B f g e) (teq (tfun A B) f g)

with der_eq : Term → Term → Term → TYPE ≔
// Computation
| der_eq_beta :
  Π(s s' : Sort), Π(u A : Term), Π(t B : Term → Term),
  der A (tsort s) → (Π(v : Var), der (B (VAR v A)) (tsort s')) → (Π(v : Var), der (t (VAR v A)) (B (VAR v A))) → der u A
  → der_eq (B u) (tapp A B (tabs A B t) u) (t u)
| der_eq_J :
  Π(s s' : Sort), Π(u A w : Term), Π(P : Term → Term → Term),
  der A (tsort s) → der u A → (Π(v1 v2 : Var), der (P (VAR v1 A) (VAR v2 (teq A u (VAR v1 A)))) (tsort s'))
  → der w (P u (trefl A u))
  → der_eq (P u (trefl A u)) (J A u P w u (trefl A u)) w
| der_eq_π1 :
  Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
  der A (tsort s) → der u A → (Π(v : Var), der (B (VAR v A)) (tsort s')) → der v (B u)
  → der_eq A (π1 A B (tpair A B u v)) u
| der_eq_π2 :
  Π(s s' : Sort), Π(u A v : Term), Π(B : Term → Term),
  der A (tsort s) → der u A → (Π(v : Var), der (B (VAR v A)) (tsort s')) → der v (B u)
  → der_eq (B u) (π2 A B (tpair A B u v)) v
// Conversion
| der_eq_conversion :
  Π(s : Sort), Π(t1 t2 T1 T2 : Term),
  der T1 (tsort s) → der T2 (tsort s)
  → der_eq T1 t1 t2 → der_eq (tsort s) T1 T2
  → der_eq T2 t1 t2
| der_eq_lift :
  Π(e u v A : Term),
  der e (teq A u v) → der_eq A u v;
