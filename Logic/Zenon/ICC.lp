// intuitionist commutative cuts

require open Logic.Zenon.FOL Logic.Zenon.ND Logic.Zenon.ND_eps;

rule ⊥E (⊥E $pbot _) $P ↪ ⊥E $pbot $P;
rule ⊥E $pbot (_ ⇒ $b) _ ↪ ⊥E $pbot $b;
rule ⊥E $pbot (∀ (λ x, $a.[x])) $t ↪ ⊥E $pbot $a.[$t];
rule ⊥E (∨E $a $b $paorb ⊥ $pabot $pbbot) $P ↪
    ∨E $a $b $paorb $P (λ pa, ⊥E ($pabot pa) $P) 
        (λ pb, ⊥E ($pbbot pb) $P);
rule ⊥E (∃E $p $pexp ⊥ $ppt) $P ↪
    ∃E $p $pexp $P (λ x pp, ⊥E ($ppt x pp) $P);

rule ∨E _ _ (⊥E $pbot _) $P _ _ ↪ ⊥E $pbot $P;
rule ∨E $a $b (∨Il $a $b $pa) _ $paP _ ↪ $paP $pa;
rule ∨E $a $b (∨Ir $a $b $pb) _ _ $pbP ↪ $pbP $pb;
rule ∨E $a $b $paorb (_ ⇒ $q) $papq $pbpq $pp ↪
    ∨E $a $b $paorb $q (λ pa, $papq pa $pp) (λ pb, $pbpq pb $pp);
rule ∨E $a $b $paorb (∀ (λ x, $r.[x])) $papq $pbpq $t ↪
    ∨E $a $b $paorb $r.[$t] (λ pa, $papq pa $t) (λ pb, $pbpq pb $t);
rule ∨E $c $d (∨E $a $b $paorb _ $pacord $pbcord) $e $pce $pde ↪
    ∨E $a $b $paorb $e
        (λ pa, ∨E $c $d ($pacord pa) $e $pce $pde)
        (λ pb, ∨E $c $d ($pbcord pb) $e $pce $pde);
rule ∨E $a $b (∃E $p $pexp ($a ∨ $b) $ppt) $e $pce $pde ↪
    ∃E $p $pexp $e
        (λ x pp, ∨E $a $b ($ppt x pp) $e $pce $pde);

rule =E $t $t (=I _) _ $pt ↪ $pt;
rule =E $t $v (⊥E $pbot ($t = $v)) $P _ ↪ ⊥E $pbot ($P $v);
rule =E $t $v (∨E $a $b $paorb ($t = $v) $patv $pbtv) $P $pPt ↪
    ∨E $a $b $paorb ($P $v)
        (λ pa, =E $t $v ($patv pa) $P $pPt)
        (λ pb, =E $t $v ($pbtv pb) $P $pPt);
rule =E $t $v (∃E $p $pexp ($t = $v) $ppt) $P $pPt ↪
    ∃E $p $pexp ($P $v) 
        (λ x pp, =E $t $v ($ppt x pp) $P $pPt);

rule ∧El $a $b (∧I $a $b $pa _) ↪ $pa;
rule ∧El $a _ (⊥E $pbot ($a ∧ _)) ↪ ⊥E $pbot $a;
rule ∧El $c $d (∨E $a $b $paorb ($c ∧ $d) $pat $pbt)  ↪
    ∨E $a $b $paorb $c (λ pa, ∧El $c $d ($pat pa)) 
        (λ pb, ∧El $c $d ($pbt pb));
rule ∧El $c $d (∃E $p $pexp ($c ∧ $d) $ppt) ↪
    ∃E $p $pexp $c (λ x pp, ∧El $c $d ($ppt x pp));

rule ∧Er $a $b (∧I $a $b _ $pb) ↪ $pb;
rule ∧Er _ $b (⊥E $pbot (_ ∧ $b)) ↪ ⊥E $pbot $b;
rule ∧Er $c $d (∨E $a $b $paorb ($c ∧ $d) $pat $pbt)  ↪
    ∨E $a $b $paorb $d (λ pa, ∧Er $c $d ($pat pa)) 
        (λ pb, ∧Er $c $d ($pbt pb));
rule ∧Er $c $d (∃E $p $pexp ($c ∧ $d) $ppt) ↪
    ∃E $p $pexp $d (λ x pp, ∧Er $c $d ($ppt x pp));

rule ∃E $p (∃I $p $t $pt) _ $pxpxP ↪ $pxpxP $t $pt;
rule ∃E _ (⊥E $pbot _) $P _ ↪ ⊥E $pbot $P;
rule ∃E $p (∨E $a $b $paorb (∃ $p) $pat $pbt) $P $pxpP ↪
    ∨E $a $b $paorb $P (λ pa, ∃E $p ($pat pa) $P $pxpP)
                        (λ pb, ∃E $p ($pbt pb) $P $pxpP);
rule ∃E $p $pexp (_ ⇒ $d) $ppt $pc ↪
    ∃E $p $pexp $d (λ x pp, $ppt x pp $pc);
rule ∃E $p (∃E $q $pexp (∃ $p) $ppt) $P $pxpP ↪
    ∃E $q $pexp $P (λ x pp, ∃E $p ($ppt x pp) $P $pxpP);
rule ∃E $p $pexp (∀ (λ x, $b.[x])) $ppt $t ↪
    ∃E $p $pexp $b.[$t] (λ x pp, $ppt x pp $t);
