/***************************************************************************
This file provides an axiom and various theorems for propositional equality.        
The theorems are grouped into sections by theme:  
- Various Simplifications
- Symmetry and polarity     
- Equalities of propositions and equalities involving ⊤ and ⊥                                
****************************************************************************/

require open tests.OK.Set tests.OK.Prop tests.OK.Eq tests.OK.Impred tests.OK.Classic;

symbol propExt x y : (π x → π y) → (π y → π x) → π (x = y);


/******************************************************************************
 *  Simplifications          
 ******************************************************************************/

// Idempotence and Contradiction for ∧ and ∨

opaque symbol ∨_idem x :
  π (x = (x ∨ x)) ≔
begin
  assume x;
  refine propExt x (x ∨ x) _ _
    {assume h2; refine ∨ᵢ₁ h2}
    {assume h1;
     refine ∨ₑ h1 _ _
       {assume h2; refine h2}
       {assume h2; refine h2}}
end;

opaque symbol ∧_idem x :
  π (x = (x ∧ x)) ≔
begin
  assume x;
  refine propExt x (x ∧ x) _ _
    {assume h1; refine ∧ᵢ h1 h1}
    {assume h1; refine ∧ₑ₁ h1}
end;

opaque symbol ∧_contra x :
  π (⊥ = (¬ x ∧ x)) ≔
begin
  assume x;
  refine propExt ⊥ (¬ x ∧ x) _ _
    {assume h1; refine ⊥ₑ h1}
    {assume h1;
     refine (∧ₑ₁ h1) (∧ₑ₂ h1)}
end;


// Disjunction/Conjunction with ⊤ / ⊥      

opaque symbol ∨⊤ x :
  π (⊤ = (x ∨ ⊤)) ≔
begin
  assume x;
  refine propExt ⊤ (x ∨ ⊤) _ _
    {assume h2; refine ∨ᵢ₂ h2}
    {assume h1; refine ⊤ᵢ}
end;

opaque symbol ∧⊤ x :
  π (x = (x ∧ ⊤)) ≔
begin
  assume x;
  refine propExt x (x ∧ ⊤) _ _
    {assume h1; refine ∧ᵢ h1 ⊤ᵢ}
    {assume h1; refine ∧ₑ₁ h1}
end;

opaque symbol ∨⊥ x :
  π (x = (x ∨ ⊥)) ≔
begin
  assume x;
  refine propExt x (x ∨ ⊥) _ _
    {assume h1; refine ∨ᵢ₁ h1}
    {assume h1;
     refine ∨ₑ h1 _ _
       {assume h2; refine h2}
       {assume h2; refine ⊥ₑ h2}}
end;

opaque symbol ∧⊥ x :
  π (⊥ = (x ∧ ⊥)) ≔
begin
  assume x;
  refine propExt ⊥ (x ∧ ⊥) _ _
    {assume h1;
     type ⊥ₑ h1;
     refine ∧ᵢ (⊥ₑ h1) h1}
    {assume h1; refine ∧ₑ₂ h1}
end;


// Negation of ⊤ and ⊥  

opaque symbol ¬⊥ :
  π (⊤ = ¬ ⊥) ≔
begin
  refine propExt ⊤ (¬ ⊥) _ _
    {assume h1 h2; refine h2}
    {assume h1; refine ⊤ᵢ}
end;

opaque symbol ¬⊤ :
  π (⊥ = ¬ ⊤) ≔
begin
  refine propExt ⊥ (¬ ⊤) _ _
    {assume h1; refine ⊥ₑ h1}
    {assume h1; refine h1 ⊤ᵢ}
end;


//Equalities on Elements   

opaque symbol eq_refl_top (T : Set) (x : τ T) :
  π (⊤ = (x = x)) ≔
begin
  assume T x;
  refine propExt ⊤ (x = x) _ _
    {assume h1; refine eq_refl x}
    {assume h1; refine ⊤ᵢ}
end;

opaque symbol eq_refl_bot (T : Set) (x : τ T) :
  π (⊥ = ¬ (x = x)) ≔
begin
  assume T x;
  refine propExt ⊥ (¬ (x = x)) _ _
    {assume h1; refine ⊥ₑ h1}
    {assume h1;
     have H1: π(x = x) → π ⊥
       {assume h2; refine h1 h2};
     refine H1 (eq_refl [T] x)}
end;

opaque symbol eq⊤ x :
  π (x = (x = ⊤)) ≔
begin
  assume x;
  refine propExt x (x = ⊤) _ _
    {assume h1;
     refine propExt x ⊤ _ _
        {assume h2; refine ⊤ᵢ}
        {assume h2; refine h1}}
    {assume h1;
     refine (ind_eq h1 (λ z, z)) ⊤ᵢ}
end;

opaque symbol ¬eq⊤ x :
  π (¬ x = ¬(x = ⊤)) ≔
begin
  assume x;
  refine propExt (¬ x) (¬(x = ⊤)) _ _
    {assume h1 h2;
     have H1_1: π x
       {refine ind_eq h2 (λ z, z) ⊤ᵢ};
     refine h1 H1_1}
    {assume h1 h2;
     refine h1 (propExt x ⊤ _ _)
        {assume h3; refine ⊤ᵢ}
        {assume h3; refine h2}}
end;


// Simplifications reflecting Classical Principles

opaque symbol em_eq x :
  π (⊤ = (¬ x ∨ x)) ≔
begin
  assume x;
  refine propExt ⊤ (¬ x ∨ x) _ _
    {assume h1;
     have em_sym: π(¬ x ∨ x)
       {refine ∨ₑ (em x) _ _
         {assume h3; refine ∨ᵢ₂ h3}
         {assume h3; refine ∨ᵢ₁ h3}};
     refine em_sym}
    {assume h1; refine ⊤ᵢ}
end;

opaque symbol ¬¬ₑ_eq x :
  π (x = ¬ ¬ x) ≔
begin
  assume x;
  refine propExt x (¬ ¬ x) _ _
    {assume h1 h2; refine h2 h1}
    {assume h1; refine ¬¬ₑ x h1}
end;


/******************************************************************************
 *  Symmetry and polarity                                                     
 ******************************************************************************/

 opaque symbol eq_sym_eq [T] (x y : τ T) :
 π((x = y) = (y = x)) ≔
begin
 assume T x y;
 have H1: π(x = y) → π(y = x)
   {assume h; symmetry; refine h};
 have H2: π(y = x) → π(x = y)
   {assume h; symmetry; refine h};
 refine propExt (x = y) (y = x) H1 H2
end;

symbol polarity_switch a b :
 π ((a = b) = (¬ a = ¬ b)) ≔
begin
 assume a b;
 refine propExt (a = b) (¬ a = ¬ b) _ _
   {assume h1;
    have H1: π(b = a)
      {symmetry; refine h1};
    refine propExt (¬ a) (¬ b) _ _
      {assume h2; refine ind_eq H1 (λ x, ¬ x) h2}
      {assume h2; refine ind_eq h1 (λ x, ¬ x) h2}}
   {assume h1;
    have H1: π(¬ b = ¬ a)
      {symmetry; refine h1};
    refine propExt a b _ _
      {assume h2;
       have H2: π(¬ ¬ a)
         {assume h3; refine h3 h2};
       refine (¬¬ₑ b) (ind_eq H1 (λ x, ¬ x) H2)}
      {assume h2;
       have H2: π(¬ (¬ b))
         {assume h3; refine h3 h2};
       refine (¬¬ₑ a) (ind_eq h1 (λ x, ¬ x) H2)}}
end;


/******************************************************************************
*  Equalities of propositions and equalities involving ⊤ and ⊥                              
******************************************************************************/

// Propositions on the LHS

opaque symbol posProp_posEqT x :
  π (x = (x = ⊤)) ≔
begin
  assume x;
  refine propExt x (x = ⊤) _ _
    {assume h1;
     refine propExt x ⊤ _ _
       {assume h2; refine ⊤ᵢ}
       {assume h2; refine h1}}
    {assume h2;
     refine ind_eq h2 (λ z, z) ⊤ᵢ}
end;

opaque symbol posProp_negEqT x :
  π (x = ¬(¬ x = ⊤)) ≔
begin
  assume x;
  refine propExt x (¬(¬ x = ⊤)) _ _
    {assume h1 h2;
     refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
     refine ∨ₑ [x] [¬ x] [x] (em x) _ _
       {assume h2; refine h2}
       {assume h2;
        have H1: π(¬ x = ⊤)
          {refine propExt (¬ x) ⊤ _ _
            {assume h3; refine ⊤ᵢ}
            {assume h3; refine h2}};
        refine ⊥ₑ (h1 H1)}}
end;

opaque symbol negProp_posEqT x :
  π (¬ x = (¬ x = ⊤)) ≔
begin
  assume x;
  refine propExt (¬ x) (¬ x = ⊤) _ _
    {assume h1;
     refine propExt (¬ x) ⊤ _ _
        {assume h2; refine ⊤ᵢ}
        {assume h2; refine h1}}
    {assume h1;
     have H1: π(¬ x = ⊤) → π(¬ x)
       {assume h2;
        refine (ind_eq h2 (λ z, z)) ⊤ᵢ};
     refine H1 h1}
end;

opaque symbol negProp_negEqT x :
  π (¬ x = ¬(x = ⊤)) ≔
begin
  assume x;
  refine propExt (¬ x) (¬ (x = ⊤)) _ _
    {assume h1 h2;
     refine h1 (ind_eq h2 (λ z, z) ⊤ᵢ)}
    {assume h1 h2;
     have H1: π(x = ⊤)
       {refine propExt x ⊤ _ _
        {assume h3; refine ⊤ᵢ}
        {assume h3; refine h2}};
     refine h1 H1}
end;

opaque symbol negProp_posEqB x :
  π (¬ x = (x = ⊥)) ≔
begin
  assume x;
  type propExt (¬ x) (x = ⊥) _ _;
  refine propExt (¬ x) (x = ⊥) _ _
    {assume h1;
     refine propExt x ⊥ _ _
       {assume h2; refine h1 h2}
       {assume h2; refine ⊥ₑ h2}}
    {assume h1;
     refine ind_eq h1 (λ y, ¬ y) (λ h: π ⊥, h)}
end;

opaque symbol negProp_negEqB x :
  π (¬ x = ¬(¬ x = ⊥)) ≔
begin
  assume x;
  refine propExt (¬ x) (¬(¬ x = ⊥)) _ _
    {assume h1 h2;
     have H1: π(⊥ = ¬ x)
       {symmetry; refine h2};
     refine ind_eq H1 (λ y, y) h1}
    {assume h1 h2;
     refine h1 _;
     refine propExt (¬ x) ⊥ _ _
       {assume h3; refine h3 h2}
       {assume h3; refine ⊥ₑ h3}}
end;

opaque symbol posProp_negEqB x :
  π (x = ¬(x = ⊥)) ≔
begin
  assume x;
  refine propExt x (¬ (x = ⊥)) _ _
    {assume h1 h2;
     refine ind_eq h2 (λ z, z ⇒ ⊥) (λ y: π ⊥, y) h1}
    {assume h1;
     refine ¬¬ₑ x _;
     assume h2;
     have H1: π(x = ⊥)
       {refine propExt x ⊥ _ _
         {assume h3; refine h2 h3}
         {assume h3; refine ⊥ₑ h3}};
     refine h1 H1}
end;

opaque symbol posProp_posEqB x :
  π (x = (¬ x = ⊥)) ≔
begin
  assume x;
  refine propExt x (¬ x = ⊥) _ _
    {assume h1;
     refine propExt (¬ x) ⊥ _ _
       {assume h2; refine h2 h1}
       {assume h2; refine ⊥ₑ h2}}
    {assume h1;
     refine ¬¬ₑ x (ind_eq h1 (λ y, ¬ y) (λ h: π ⊥, h))}
end;


// Equalities on the LHS

opaque symbol negEqT_posProp x :
  π (¬(¬ x = ⊤) = x) ≔
begin
  assume x;
  symmetry;
  refine propExt x (¬ (¬ x = ⊤)) _ _
    {assume h1 h2;
     refine ((ind_eq h2 (λ z, z)) ⊤ᵢ) h1}
    {assume h1;
     refine ∨ₑ (em x) _ _
        {assume h2; refine h2}
        {assume h2;
         have H1: π(¬ x = ⊤)
          {refine propExt (¬ x) ⊤ _ _
            {assume h3; refine ⊤ᵢ}
            {assume h3; refine h2}};
         refine ⊥ₑ (h1 H1)}}
end;

opaque symbol negEqT_negProp x :
  π (¬(x = ⊤) = ¬ x) ≔
begin
  assume x;
  symmetry;
  refine propExt (¬ x) (¬ (x = ⊤)) _ _
    {assume h1 h2;
     refine h1 (ind_eq h2 (λ z, z) ⊤ᵢ)}
    {assume h1 h2;
     have H1: π(x = ⊤)
        {refine propExt x ⊤ _ _
            {assume h3; refine ⊤ᵢ}
            {assume h3; refine h2}};
    refine h1 H1}
end;

opaque symbol posEqT_posProp x :
  π ((x = ⊤) = x) ≔
begin
  assume x;
  symmetry;
  refine propExt x (x = ⊤) _ _
    {assume h1;
     refine propExt x ⊤ _ _
        {assume h2; refine ⊤ᵢ}
        {assume h2; refine h1}}
    {assume h2;
     refine ind_eq h2 (λ z, z) ⊤ᵢ}
end;

opaque symbol posEqT_negProp x :
  π ((¬ x = ⊤) = ¬ x) ≔
begin
  assume x;
  symmetry;
  refine propExt (¬ x) (¬ x = ⊤) _ _
    {assume h1;
     refine propExt (¬ x) ⊤ _ _
        {assume h2; refine ⊤ᵢ}
        {assume h2; refine h1}}
    {assume h1;
     have H1: π(¬ x = ⊤) → π(¬ x)
       {assume h2;
        refine (ind_eq h2 (λ z, z)) ⊤ᵢ};
     refine H1 h1}
end;

opaque symbol posEqT_l_posProp x :
  π ((⊤ = x) = x) ≔
begin
  assume x;
  refine propExt (⊤ = x) x _ _
    {assume h1;
     have H1: π x → π x
       {assume h2; refine h2};
     refine (ind_eq h1 (λ z, z ⇒ x) H1) ⊤ᵢ}
    {assume h1;
     refine propExt ⊤ x _ _
        {assume h2; refine h1}
        {assume h2; refine ⊤ᵢ}}
end;

opaque symbol posEqB_l_negProp x :
  π ((⊥ = x) = ¬ x) ≔
begin
  assume x;
  refine propExt (⊥ = x) (¬ x) _ _
    {assume h1;
     have H1: π x → π x
       {assume h2; refine h2};
     refine ind_eq h1 (λ z, x ⇒ z) H1}
    {assume h1;
     refine propExt ⊥ x _ _
       {assume h2; refine ⊥ₑ h2}
       {assume h2; refine h1 h2}}
end;

