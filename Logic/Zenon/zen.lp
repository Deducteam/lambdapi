require open Logic.Zenon.FOL Logic.Zenon.LL Logic.Zenon.ND Logic.Zenon.ND_eps
             Logic.Zenon.ND_eps_full Logic.Zenon.ND_eps_aux Logic.Zenon.LL_ND;

symbol Type : TYPE;

injective symbol τ : Type → TYPE;

constant symbol ι  : Type;

symbol nnpp p : ϵ (¬ ¬ p) → ϵ p;

constant symbol select : Π (a : Type), τ a;

rule τ ι ↪ κ;

symbol foralltype : (Type → Prop) → Prop;
symbol existstype : (Type → Prop) → Prop;

symbol ∀α [a] : (τ a → Prop) → Prop; notation ∀α quantifier;
rule @∀α ι ↪ ∀;

symbol ∃α [a] : (τ a → Prop) → Prop; notation ∃α quantifier;
rule @∃α ι ↪ ∃;

symbol =α [a] : τ a → τ a → Prop; notation =α infix 12;
rule @=α ι $t $u ↪ $t = $u;

symbol Rfalse : ϵ ⊥ → ϵ ⊥; 
rule Rfalse ↪ R⊥;

symbol Rnottrue : ϵ (¬ ⊤) → ϵ ⊥;
rule Rnottrue ↪ R¬⊤;

symbol Raxiom : Π (p : Prop), ϵ p → ϵ (¬ p) → ϵ ⊥;
rule Raxiom ↪ Rax;

symbol Rnoteq : Π (a : Type) (t : τ a), ϵ (¬ (t =α t)) → ϵ ⊥;
rule Rnoteq ι ↪ R≠;

symbol Reqsym a (t u : τ a) : ϵ (t =α u) → ϵ (¬ (u =α t)) → ϵ ⊥;
rule Reqsym ι ↪ R=;

symbol Rnotnot p : (ϵ p → ϵ ⊥) → ϵ (¬ (¬ p)) → ϵ ⊥;
rule Rnotnot ↪ R¬¬;

symbol Rand p q : (ϵ p → ϵ q → ϵ ⊥) → ϵ (p ∧ q) → ϵ ⊥;
rule Rand ↪ R∧;

symbol Ror p q : (ϵ p → ϵ ⊥) → (ϵ q → ϵ ⊥) → ϵ (p ∨ q) → ϵ ⊥;
rule Ror ↪ R∨;

symbol Rimply p q :  (ϵ (¬ p) → ϵ ⊥) → (ϵ q → ϵ ⊥) → ϵ (p ⇒ q) → ϵ ⊥;
rule Rimply ↪ R⇒;

symbol Requiv p q : 
  (ϵ (¬ p) → ϵ (¬ q) → ϵ ⊥) → (ϵ p → ϵ q → ϵ ⊥) → ϵ (p ⇔ q) → ϵ ⊥;
rule Requiv ↪ R⇔;

symbol Rnotand p q : 
  (ϵ (¬ p) → ϵ ⊥) → (ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ∧ q)) → ϵ ⊥;
rule Rnotand ↪ R¬∧;

symbol Rnotor p q : (ϵ (¬ p) → ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ∨ q)) → ϵ ⊥;
rule Rnotor ↪ R¬∨;

symbol Rnotimply p q : (ϵ p → ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ⇒ q)) → ϵ ⊥;
rule Rnotimply ↪ R¬⇒;

symbol Rnotequiv p q :
  (ϵ (¬ p) → ϵ q → ϵ ⊥) → (ϵ p → ϵ (¬ q) → ϵ ⊥) → ϵ (¬ (p ⇔ q)) → ϵ ⊥;
rule Rnotequiv ↪ R¬⇔;

symbol Rex a p : (Π (t : τ a), ϵ (p t) → ϵ ⊥) → ϵ (∃α p) → ϵ ⊥;
rule Rex ι ↪ R∃;

symbol Rall a p t : (ϵ (p t) → ϵ ⊥) → ϵ (@∀α a p) → ϵ ⊥;
rule Rall ι ↪ R∀;

symbol Rnotex a (p : (τ a → Prop)) (t : τ a) : 
  (ϵ (¬ (p t)) → ϵ ⊥) → ϵ (¬ (∃α p)) → ϵ ⊥;
rule Rnotex ι ↪ R¬∃;

symbol Rnotall a p : (Π (t : τ a), ϵ (¬ (p t)) → ϵ ⊥) → ϵ (¬ (@∀α a p)) → ϵ ⊥;
rule Rnotall ι ↪ R¬∀;

//symbol Rextype (p : (Type → Prop)) : 
//  (Π (a : Type), ϵ (p a) → ϵ ⊥) → ϵ (existstype p) → ϵ ⊥;

//symbol Ralltype (p : (Type → Prop)) a :
//  (ϵ (p a) → ϵ ⊥) → ϵ (foralltype p) → ϵ ⊥;

//symbol Rnotextype (p : (Type → Prop)) a :
//  (ϵ (¬ (p a)) → ϵ ⊥) → ϵ (¬ (existstype p)) → ϵ ⊥;

//symbol Rnotalltype (p : (Type → Prop)) : 
//  (Π (a : Type), ϵ (¬ (p a)) → ϵ ⊥) → ϵ (¬ (foralltype p)) → ϵ ⊥;

symbol Rsubst a (p : (τ a → Prop)) (t1 t2 : τ a) :
  (ϵ (¬ (t1 =α t2)) → ϵ ⊥) → (ϵ (p t2) → ϵ ⊥) → ϵ (p t1) → ϵ ⊥;
rule Rsubst ι ↪ Rσ;

symbol Rconglr a (p : (τ a → Prop)) (t1 t2 : τ a) :
  (ϵ (p t2) → ϵ ⊥) → ϵ (p t1) → ϵ (t1 =α t2) → ϵ ⊥;
rule Rconglr ι ↪ R≡r;

symbol Rcongrl a (p : (τ a → Prop)) (t1 t2 : τ a) :
  (ϵ (p t2) → ϵ ⊥) → ϵ (p t1) → ϵ (t2 =α t1) → ϵ ⊥;
rule Rcongrl ι ↪ R≡l;
