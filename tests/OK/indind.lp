/* example of inductive-inductive type:

contexts and types in dependent type theory

page 31 of Forsberg's 2013 PhD thesis "Inductive-inductive definitions"
http://www.cs.swan.ac.uk/~csetzer/articlesFromOthers/nordvallForsberg/phdThesisForsberg.pdf
*/

// definitions needed for expressing induction principles

constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;

injective symbol π : Prop → TYPE;
builtin "Prf" ≔ π;

// contexts
inductive Con : TYPE ≔
| □ : Con
| ⋅ Γ : Ty Γ → Con

// types
with Ty : Con → TYPE ≔
| U Γ : Ty Γ
| P Γ (a : Ty Γ) : Ty (⋅ Γ a) → Ty Γ;

notation ⋅ infix left 10;

/* generated induction principles:

print ind_Con;
print ind_Ty;

after some renamings we get:

symbol ind_Con:
  Π p: Con → Prop,
  Π q: (Π Γ: Con, Ty Γ → Prop),
  π (p □) →
  (Π Γ: Con, π (p Γ) → Π A: Ty Γ, π (q Γ A) → π (p (Γ ⋅ A))) →
  (Π Γ: Con, π (p Γ) → π (q Γ (U Γ))) →
  (Π Γ: Con, π (p Γ) → Π A: Ty Γ, π (q Γ A) → Π B: Ty (Γ ⋅ A), π (q (Γ ⋅ A) B) → π (q Γ (P Γ A B))) →
  Π Γ: Con, π (p Γ)

rules:

  ind_Con $p $q $h□ $h⋅ $hU $hP □ ↪ $h□

  ind_Con $p $q $h□ $h⋅ $hU $hP ($Γ ⋅ $A)
  ↪ $h⋅ $Γ (ind_Con $p $q $h□ $h⋅ $hU $hP $Γ)
        $A (ind_Ty $p $q $h□ $h⋅ $hU $hP $Γ $A)

symbol ind_Ty:
  Π p: (Con → Prop),
  Π q: (Π Γ: Con, Ty Γ → Prop),
  π (p □) →
  (Π Γ: Con, π (p Γ) → Π A: Ty Γ, π (q Γ A) → π (p (Γ ⋅ A))) →
  (Π Γ: Con, π (p Γ) → π (q Γ (U Γ))) →
  (Π Γ: Con, π (p Γ) → Π A: Ty Γ, π (q Γ A) →
                       Π B: Ty (Γ ⋅ A), π (q (Γ ⋅ A) B) → π (q Γ (P Γ A B))) →
  Π Γ: Con, Π A: Ty Γ, π (q Γ A)

rules:

  ind_Ty $p $q $h□ $h⋅ $hU $hP $Γ (U _)
  ↪ $hU $Γ (ind_Con $p $q $h□ $h⋅ $hU $hP $Γ)

  ind_Ty $p $q $h□ $h⋅ $hU $hP $Γ (P _ $A $B)
  ↪ $hP $Γ (ind_Con $p $q $h□ $h⋅ $hU $hP $Γ)
        $A (ind_Ty $p $q $h□ $h⋅ $hU $hP $Γ $A)
        $B (ind_Ty $p $q $h□ $h⋅ $hU $hP ($Γ ⋅ $A) $B)
*/

// a more dependent induction principle can be defined by hand:

symbol ind_Con' :
  Π p : Con → Prop,
  Π q : (Π Γ, π (p Γ) → Ty Γ → Prop),
  π (p □) →
  Π h⋅ : (Π Γ, Π hΓ : π (p Γ), Π A, π (q Γ hΓ A) → π (p (Γ ⋅ A))),
  (Π Γ, Π hΓ : π (p Γ), π (q Γ hΓ (U Γ))) →
  (Π Γ, Π hΓ : π (p Γ), Π A, Π hA : π (q Γ hΓ A), Π B,
    π (q (Γ ⋅ A) (h⋅ Γ hΓ A hA) B) → π (q Γ hΓ (P Γ A B))) →
  Π Γ, π (p Γ);

symbol ind_Ty' :
  Π p : Con → Prop,
  Π q : (Π Γ, π (p Γ) → Ty Γ → Prop),
  π (p □) →
  Π h⋅ : (Π Γ, Π hΓ : π (p Γ), Π A, π (q Γ hΓ A) → π (p (Γ ⋅ A))),
  (Π Γ, Π hΓ : π (p Γ), π (q Γ hΓ (U Γ))) →
  (Π Γ, Π hΓ : π (p Γ), Π A, Π hA : π (q Γ hΓ A), Π B,
    π (q (Γ ⋅ A) (h⋅ Γ hΓ A hA) B) → π (q Γ hΓ (P Γ A B))) →
  Π Γ, Π hΓ : π (p Γ), Π A, π (q Γ hΓ A);

rule ind_Con' _ _ $h□ _ _ _ □ ↪ $h□;

rule ind_Con' $p $q $h□ $h⋅ $hU $hP ($Γ ⋅ $A)
↪ let hΓ ≔ ind_Con' $p $q $h□ $h⋅ $hU $hP $Γ in
  $h⋅ $Γ hΓ $A (ind_Ty' $p $q $h□ $h⋅ $hU $hP $Γ hΓ $A);

rule ind_Ty' $p $q $h□ $h⋅ $hU $hP $Γ $hΓ (U _)
↪ $hU $Γ $hΓ;

rule ind_Ty' $p $q $h□ $h⋅ $hU $hP $Γ $hΓ (P _ $A $B)
↪ let hA ≔ ind_Ty' $p $q $h□ $h⋅ $hU $hP $Γ $hΓ $A in
  let hΓ⋅A ≔ $h⋅ $Γ $hΓ $A hA in
  $hP $Γ $hΓ $A hA $B (ind_Ty' $p $q $h□ $h⋅ $hU $hP ($Γ ⋅ $A) hΓ⋅A $B);
