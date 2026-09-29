/* Library on Meta-Theorems for Disjunctions

-------------------

The library proves the following meta-theorems:

** n-ary Natural Deduction rules:
   - ∨ᵢₙ is the n-ary versions of the introduction rule for ∨.
   - ∨ₑₙ is the n-ary version of the elimination rule for ∨.

** Permute:
   The theorem is instantiated with:
   - A list of natural numbers representing a permutation.
   - A list of terms of type `o` representing a clause.

   The theorem verifies that the permuted clause still contains all literals of the original clause. 
   If so, it maps the disjunction of the original clause to the disjunction after the permutation.

** Delete:
   The theorem is instantiated with three lists:
   1. A list of natural numbers representing the indices of literals in the original clause. 
     For literals occurring multiple times, the index of the first occurrence is used for all of the
     subsequent occurrences. For example, for `π (l0 ∨ l1 ∨ l2 ∨ l1)`, this list would be `(0, 1, 2, 1)`.
   2. A second list of natural numbers indicating the desired positions of the literals in the resulting clause.
     If for instance the second occurrence of `l1` in `π (l0 ∨ l1 ∨ l2 ∨ l1)` should be deleted, the 
     derived clause would be `π (l0 ∨ l1 ∨ l2)`, and the list that must be provided would be (0, 1, 2).
     To delete the first occurrence of `l1`, and derive the clause `π (l0 ∨ l2 ∨ l1)`, the list would 
     be (0, 2, 1).
   3. A list of terms of type `o`, representing literals.

   The resulting theorem verifies if each literal from the original clause is still present at least once 
   in the derived clause. If so, it maps the disjunction of the original literals to the disjunction after 
   the desired double literal deletion. This approach allows multiple identical literals to be deleted at once.

** DeleteDoubles:
   A convenience version of Delete, where duplicate occurrences of literals are removed automatically,
   leaving only the first occurrence.

   The theorem is instantiated with:
   - A list of natural numbers representing the indices of literals in the original clause. As in Delete,
     when a literal occurs multiple times, all occurrences are represented using the index of its first occurrence.
   - A list of terms of type `o`, representing literals.

   The theorem maps the original clause directly to a version where all duplicate literals have been removed.

** Transform:
   This theorem is useful when a rule is applied to only one literal of a clause. 
   For example, consider the clause `π (l0 ∨ l1 ∨ l2 ∨ l3)` and an inference rule `π l2 → π l2'`. 
   The transformation theorem can be instantiated with:
   - The list of terms of type `o` representing the original clause.
   - The position of the literal being affected.
   - The inference rule.

   The resulting term maps the original disjunction to one with the transformed literal.

---

** General Concept:
   The general idea behind the permutation and double literal deletion theorems is to evaluate a list of natural 
   numbers representing the positions of literals after respective operations with respect to the original clause. 
   A computation ensures the operation is admissible:
   - In the case of permutations, all literals must still be present in the permuted clause.
   - In the case of double literal deletion, each literal must still be present at least once.
   If these conditions are fulfilled, the corresponding argument in the theorem will compute to `π ⊤` and can simply
   be instantiated with `⊤ᵢ` (examples are given below).

---

** Defined Operations:
                        `x ∈ₙ l`: Special case of ∈ for natural numbers and equality relation `eqn`
                   `literal n l`: Returns the element of the list `l` of terms of type `o` at index `n`.
                 `literals ln l`: Takes as arguments a list `ln` of natural numbers and a list `l` of terms of 
                                  type `o` and returns a list of  the elements of `l` ordered according to the 
                                  indices in `ln`.
                        `disj l`: Returns the disjunction of all literals in the list `l`.
                      `l1 ⊆ₙ l2`: Special case of ⊆ for natural numbers and equality relation `eqn`
      `preserves_contents ln lo`: Takes a list of natural numbers (`ln`) and a list of terms of type `o` (`lo`) 
                                  as arguments. Returns `true` if every index of `lo` is included in `ln`.
*/

require open tests.OK.List tests.OK.PropExt;
  

////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////// lemmas ////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Define some notations corresponding to standard library symbols

symbol ∈ₙ ≔ ∈ eqn;
notation ∈ₙ infix right 40;

symbol literal ≔ nth ⊥;
assert l0 l1 l2 ⊢ literal (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) 1 ≡ l1;

symbol literals ≔ nths ⊥;
assert l0 l1 l2 ⊢ literals (l0 ⸬ l1 ⸬ l2  ⸬ l1 ⸬ □) (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) ≡ l1 ⸬ (l2  ⸬ (l0 ⸬ (l1 ⸬ □)));


// n-ary disj

symbol disj : 𝕃 o → τ o;
rule disj ($l1 ⸬ ($c ⸬ $l)) ↪ ($l1 ∨ disj ($c ⸬ $l))
with disj ($l1 ⸬ □) ↪ $l1 
with disj □ ↪ ⊥;

assert l0 l1 l2 ⊢ π (disj (l0 ⸬ l1 ⸬ l2  ⸬ l1 ⸬ □)) ≡ π (l0 ∨ (l1 ∨ (l2  ∨ l1)));

opaque symbol disj_head (l0 : τ o) (l : 𝕃 o) : 
    π l0 → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine h1}   
        {assume x0 l1 h1 h2; 
        refine ∨ᵢ₁ h2}
end; 

opaque symbol disj_tail (l0 : τ o) (l : 𝕃 o) : 
    π (disj l) → π (disj (l0 ⸬ l)) ≔
begin
    assume l0;
    induction
        {assume h1;
        refine ⊥ₑ h1}
        {assume x1 l1 h1 h2;
        refine ∨ᵢ₂ h2}
end;

opaque symbol disj_correct (l0 : τ o) (l : 𝕃 o) : 
    π (disj (l0 ⸬ l) = (l0 ∨ disj l)) ≔
begin
    assume l0;
    induction
        {simplify; 
        rewrite ∨⊥; 
        reflexivity}
        {simplify;
        assume x l h0; 
        reflexivity}
end;

opaque symbol disj_++_correct (l l' : 𝕃 o) : 
    π (disj (l ++ l') = (disj l ∨ disj l')) ≔
begin
    induction
        {simplify; assume x; 
        rewrite ⊥∨; reflexivity}
        {simplify; assume l0 l h0 l'; 
        rewrite disj_correct; rewrite disj_correct;
        rewrite h0 l'; rewrite ∨_assoc;
        reflexivity}
end;

opaque symbol lit_imp_disj (c: 𝕃 o) (ks: 𝕃 nat) : 
    π (`∃ x, literal c x ∧ x ∈ₙ ks) → π (disj (literals c ks)) ≔
begin
    assume c;
    induction
    {assume h1;
        have H0: Π x: τ nat, π ((λ x1, literal c x1 ∧ ⊥) x) → π ⊥
        {assume x h2;
        refine ∧ₑ₂ h2};
        refine ∃ₑ h1 H0}
    {assume n l h1 h2;
        have H1: Π x: τ nat,
        π ((λ x1, literal c x1 ∧ (eqn x1 n or x1 ∈ₙ l)) x)
            → π (disj (literal c n ⸬ literals c l))
        {assume m h3;
        have H0: π (eqn m n ∨ m ∈ₙ l)
            {refine ∨_istrue [eqn m n] [m ∈ₙ l] (∧ₑ₂ h3)};
        have H1: π (eqn m n) → π (disj (literal c n ⸬ literals c l))
            {assume h4;
            have H1_0: π (literal c n)
                {have H1_0_0: π (n = m)
                {symmetry;
                refine eqn_correct m n h4};
                rewrite H1_0_0;
                refine ∧ₑ₁ h3};
            refine disj_head (literal c n) (literals c l) H1_0};
        have H2: π (m ∈ₙ l) → π (disj (literal c n ⸬ literals c l))
            {assume h4;
            have H2_0: π (`∃ x, literal c x ∧ x ∈ₙ l)
                {have H2_0_0: π ((λ x, literal c x ∧ x ∈ₙ l) m)
                {refine ∧ᵢ (∧ₑ₁ h3) h4};
                refine ∃ᵢ m H2_0_0};
            refine disj_tail (literal c n) (literals c l) (h1 H2_0)};
        refine ∨ₑ H0 H1 H2};
        refine ∃ₑ h2 H1}
end;

opaque symbol disj_imp_lit (c: 𝕃 o) (ks: 𝕃 nat): 
    π (disj (literals c ks)) → π (`∃ (x : τ nat), literal c x ∧ x ∈ₙ ks) ≔
begin
    assume c;
    induction
    {assume h1;
        refine ⊥ₑ h1}
    {assume l0 ks h1 h2;
        have H0: π (literal c l0 ∨ disj (literals c ks))
        {refine =⇒ (disj_correct (literal c l0) (literals c ks)) h2};
        have H1: π (literal c l0) → π (`∃ x, literal c x ∧ x ∈ₙ (l0 ⸬ ks))
        {assume h3;
        have H1_0: π (literal c l0)
            {refine h3};
        have H1_1: π ((λ x, literal c x ∧ x ∈ₙ (l0 ⸬ ks)) l0)
            {refine ∧ᵢ H1_0
            (mem_head eqn l0 ks
                (istrue=true (eqn_complete l0 l0 (eq_refl l0))))};
        refine ∃ᵢ l0 H1_1};
        have H2: π (disj (literals c ks)) → π (`∃ x, literal c x ∧ x ∈ₙ (l0 ⸬ ks))
        {assume h3;
        have H2_0: Π x: τ nat,
            π ((λ x1, literal c x1 ∧ x1 ∈ₙ ks) x)
                → π (`∃ x1, literal c x1 ∧ x1 ∈ₙ (l0 ⸬ ks))
            {assume n h4;
            have H2_0_0: π ((λ x, literal c x ∧ x ∈ₙ (l0 ⸬ ks)) n)
                {refine ∧ᵢ (∧ₑ₁ h4) (mem_tail eqn n l0 ks (∧ₑ₂ h4))};
            refine ∃ᵢ n H2_0_0};
        refine ∃ₑ (h1 h3) H2_0};
        refine ∨ₑ H0 H1 H2}
end;   


// ⊆

symbol ⊆ₙ ≔ ⊆ eqn;
notation ⊆ₙ infix right 30.000000;

assert ⊢ (0 ⸬ 1 ⸬ □) ⊆ₙ (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) ≡ true;

opaque symbol ⊆ₙ_el (n: τ nat) (σ: 𝕃 nat) (ln: 𝕃 nat): 
    π (ln ⊆ₙ σ) → π (n ∈ₙ ln) → π (n ∈ₙ σ) ≔
begin
    assume n σ;
    induction
    {assume h1 h2;
        refine ⊥ₑ h2}
    {assume m ln h1 h2 h3;
        have H1: π (eqn n m) → π (n ∈ₙ σ)
        {assume h4;
        have H1_0: π (n = m)
            {refine eqn_correct n m h4};
        rewrite H1_0;
        refine andₑ₁ [∈ eqn m σ] [⊆ eqn ln σ] h2};
        have H2: π (n ∈ₙ ln) → π (n ∈ₙ σ)
            {assume h4;
            refine h1 (andₑ₂ [∈ eqn m σ] [⊆ eqn ln σ] h2) h4};
        refine orₑ [eqn n m] [n ∈ₙ ln] (n ∈ₙ σ) h3 H1 H2}
end;


// preserves_contents

symbol preserves_contents: 𝕃 nat → 𝕃 o → 𝔹;
rule preserves_contents  $f $l ↪ indexes $l ⊆ₙ $f;

assert l0 l1 l2 ⊢ 
    preserves_contents (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) ≡ true;

opaque symbol preserves_contents_correct (n: τ nat) (σ : 𝕃 nat) (l: 𝕃 o) : 
    π (preserves_contents σ l) →  π (n ∈ₙ indexes l) → π (n ∈ₙ σ) ≔
begin
    assume n σ l h1 h2;
    refine ⊆ₙ_el n σ (indexes l) h1 h2;   
end;


////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// meta-theorems ////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

///////////////////// Natural Deduction rules over lists ///////////////////////

// ∨ᵢₙ
opaque symbol ∨ᵢₙ (c0 : 𝕃 o) (c1 : 𝕃 o) (c2 : 𝕃 o) : 
    π (disj c1) → π (disj (c0 ++ c1 ++ c2))≔
begin
    induction
        {assume x c2 h0; simplify;
        rewrite disj_++_correct; refine ∨ᵢ₁ h0}
        {assume x0 l h0 x1 x2 h1; simplify;  
        rewrite disj_correct; refine ∨ᵢ₂ (h0 x1 x2 h1)}
end;

// ∨ₑₙ 
opaque symbol ∨ₑₙ (n : ℕ) (c : 𝕃 o) [r : Prop] : 
    π (disj c) → π (literal c n ⇒ r) → π (disj (rem_nth c n) ⇒ r) → π r ≔
begin
    induction
        {induction
            {assume x h0 h1 h2; refine ⊥ₑ h0}
            {assume l0 l h0 r h1 h2 h3;
             refine ∨ₑ (=⇒ (disj_correct l0 l) h1) _ _
                {assume h4; refine h2 h4}
                {assume h4; refine h3 h4}}}
        {assume n h0; induction
            {assume r h1 h2 h3; refine ⊥ₑ h1}
            {assume l0 l h1 r h2 h3 h4;
            have H1 : π ((l0  ∨ (disj (rem_nth l n))) ⇒ r)
                    {rewrite left disj_correct; refine h4};
            refine ∨ₑ (em l0) _ _
                {assume h5;
                refine H1 ((∨ᵢ₁ [l0] [disj (rem_nth l n)]) h5)}
                {assume h5;
                have l0is⊥ : π (⊥ = l0)
                    {refine propExt ⊥ l0 _ _
                        {assume h6; refine ⊥ₑ h6}
                         {assume h6; refine h5 h6}};
                refine h0 l r _ h3 _
                    {rewrite left ⊥∨; rewrite l0is⊥;
                    rewrite left disj_correct l0 l; refine h2}
                    {rewrite left ⊥∨ (disj (rem_nth l n)); 
                    rewrite l0is⊥; refine H1}}}}        
end;


// permutation theorem /////////////////////////////////////////////////////////
opaque symbol permute (σ : 𝕃 nat) (c: 𝕃 o) : 
    π (preserves_contents σ c) → π(disj c) → π(disj (literals c σ)) ≔
begin
    assume σ c h1 h2;
    have H1: Π x: τ nat,
        π ((λ x1, literal c x1 ∧ x1 ∈ₙ indexes c) x)
        → π (`∃ y, literal c y ∧ y ∈ₙ σ)
        {assume x0 h3;
        refine ∃ᵢ x0 (∧ᵢ (∧ₑ₁ h3) (preserves_contents_correct x0 σ c h1 (∧ₑ₂ h3)))};
    have H2: π (`∃ y, literal c y ∧ y ∈ₙ σ)
        {have H3: π (disj (nths ⊥ c (indexes c)))
            {rewrite nths_indexes_id ⊥ c;
            refine h2};
        refine ∃ₑ (disj_imp_lit c (indexes c) H3) H1};
    refine lit_imp_disj c σ H2
end;

assert l0 l1 l2 ⊢ permute (1 ⸬ 2 ⸬ 0 ⸬ 3 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ l0 ⸬ □) ⊤ᵢ : 
    π (l0 ∨ l1 ∨ l2 ∨ l0) → π (l1 ∨ l2 ∨ l0 ∨ l0);


// double literal deletion theorem /////////////////////////////////////////////
opaque symbol delete (id_list : 𝕃 nat) (output_list : 𝕃 nat) (c: 𝕃 o) : 
    π (id_list ⊆ₙ output_list) → π(disj (literals c id_list)) → π(disj (literals c output_list)) ≔
begin
    assume id_list output_list c h1 h2;
    refine lit_imp_disj c output_list _;
    refine ∃ₑ (disj_imp_lit c id_list h2) _;
    assume n h3;
    refine ∃ᵢ n (∧ᵢ (∧ₑ₁ h3)
        (⊆ₙ_el n output_list id_list h1 (∧ₑ₂ h3)))
end; 

assert l0 l1 l2 ⊢ delete (0 ⸬ 1 ⸬ 0 ⸬ 0 ⸬ 2 ⸬ □) (0 ⸬ 1 ⸬ 2 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ □) ⊤ᵢ: 
    π (l0 ∨ l1 ∨ l0 ∨ l0 ∨ l2) → π (l0 ∨ l1 ∨ l2);

    
opaque symbol deleteDoubles (id_list : 𝕃 nat) (c: 𝕃 o) : 
    π(disj (literals c id_list)) → π(disj (literals c (undup_first eqn id_list))) ≔
begin
    assume id_list c h2;
    refine delete id_list (undup_first eqn id_list) c (subset_undup_first eqn eqn_correct eqn_refl eqn_sym id_list) h2;
end; 

assert l0 l1 l2 ⊢ deleteDoubles (0 ⸬ 1 ⸬ 0 ⸬ 0 ⸬ 2 ⸬ □) (l0 ⸬ l1 ⸬ l2 ⸬ □): 
    π (l0 ∨ l1 ∨ l0 ∨ l0 ∨ l2) → π (l0 ∨ l1 ∨ l2);


// transformation theorem //////////////////////////////////////////////////////
opaque symbol transform [l : τ o] (c: 𝕃 o) (n : τ nat) : 
π (literal c n ⇒ l) → π (disj c) → π (disj (set_nth ⊥ c n l)) ≔
begin
    assume l;
    induction
    {assume x h1 h2;
        refine ⊥ₑ h2}
    {assume x clause h1;
        induction
            {assume h2 h3;
            have H0: π (x ∨ disj clause)
                {refine =⇒ (disj_correct x clause) h3};
            have H1: π x → π (disj (l ⸬ clause))
                {assume h4;
                refine disj_head l clause (h2 h4)};
            have H2: π (disj clause) → π (disj (l ⸬ clause))
                {assume h4;
                refine disj_tail l clause h4};
            refine ∨ₑ H0 H1 H2}
            {assume n h2 h3 h4;
            have H00: π (x ∨ disj clause)
                {refine =⇒ (disj_correct x clause) h4};
            have H10: π x → π (disj (x ⸬ set_nth ⊥ clause n l))
                {assume h5;
                refine disj_head x (set_nth ⊥ clause n l) h5};
            have H20: π (disj clause) → π (disj (x ⸬ set_nth ⊥ clause n l))
                {assume h5;
                have H2_0: π (disj (set_nth ⊥ clause n l))
                    {refine h1 n h3 h5};
                refine disj_tail x (set_nth ⊥ clause n l) H2_0};
            refine ∨ₑ H00 H10 H20}}
end;

assert l0 l1 l2 l2' ⊢ transform [l2'] (l0 ⸬ l1 ⸬ l2 ⸬ l1 ⸬ □) 2 : 
    (π l2 → π l2') →  π (l0 ∨ l1 ∨ l2 ∨ l1) → π (l0 ∨ l1 ∨ l2' ∨ l1);