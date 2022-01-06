// classical commutative cuts

require open Logic.Zenon.FOL Logic.Zenon.ND Logic.Zenon.ND_eps;

symbol nnpp p : ϵ (¬ ¬ p) → ϵ p;

rule ⊥E $pb $P ↪ nnpp $P (λ _, $pb);

rule ∨E $a $b (∨Il $a $b $pa) _ $paP _ ↪ $paP $pa;
rule ∨E $a $b (∨Ir $a $b $pb) _ _ $pbP ↪ $pbP $pb;
rule ∨E $a $b $paorb (_ ⇒ $q) $papq $pbpq $pp ↪
    ∨E $a $b $paorb $q (λ pa, $papq pa $pp) (λ pb, $pbpq pb $pp);
rule ∨E $c $d (∨E $a $b $paorb _ $pacord $pbcord) $e $pce $pde ↪
    ∨E $a $b $paorb $e
        (λ pa, ∨E $c $d ($pacord pa) $e $pce $pde)
        (λ pb, ∨E $c $d ($pbcord pb) $e $pce $pde);
rule ∨E $a $b $paorb (∀ (λ x, $r.[x])) $papq $pbpq $t ↪
    ∨E $a $b $paorb $r.[$t] (λ pa, $papq pa $t) (λ pb, $pbpq pb $t);
rule ∨E $a $b (∃E $p $pexp ($a ∨ $b) $ppt) $e $pce $pde ↪
    ∃E $p $pexp $e
        (λ x pp, ∨E $a $b ($ppt x pp) $e $pce $pde);
rule ∨E $a $b (nnpp ($a ∨ $b) $pnnab) $c $pac $pbc ↪
  nnpp $c (λ h1 : ϵ (¬ $c), $pnnab
    (λ h2 : ϵ ($a ∨ $b), h1 (∨E $a $b h2 $c $pac $pbc)));

rule =E $t $t (=I $t) _ $pt ↪ $pt;
rule =E $t $v (∨E $a $b $paorb ($t = $v) $patv $pbtv) $P $pPt ↪
    ∨E $a $b $paorb ($P $v)
        (λ pa, =E $t $v ($patv pa) $P $pPt)
        (λ pb, =E $t $v ($pbtv pb) $P $pPt);
rule =E $t $v (∃E $p $pexp ($t = $v) $ppt) $P $pPt ↪
    ∃E $p $pexp ($P $v)
      (λ x pp, =E $t $v ($ppt x pp) $P $pPt);
rule =E $t $v (nnpp ($t = $v) $pnntv) $c $pct ↪
  nnpp ($c $v) (λ h1 : ϵ (¬ ($c $v)), $pnntv
    (λ h2 : ϵ ($t = $v), h1 (=E $t $v h2 $c $pct)));

rule ∧El $a $b (∧I $a $b $pa _) ↪ $pa;
rule ∧El $c $d (∨E $a $b $paorb ($c ∧ $d) $pat $pbt)  ↪
    ∨E $a $b $paorb $c (λ pa, ∧El $c $d ($pat pa))
      (λ pb, ∧El $c $d ($pbt pb));
rule ∧El $c $d (∃E $p $pexp ($c ∧ $d) $ppt) ↪
    ∃E $p $pexp $c (λ x pp, ∧El $c $d ($ppt x pp));
rule ∧El $a $b (nnpp ($a ∧ $b) $pnnab) ↪
  nnpp $a (λ h1 : ϵ (¬ $a), $pnnab
    (λ h2 : ϵ ($a ∧ $b), h1 (∧El $a $b h2)));

rule ∧Er $a $b (∧I $a $b _ $pb) ↪ $pb;
rule ∧Er $c $d (∨E $a $b $paorb ($c ∧ $d) $pat $pbt)  ↪
    ∨E $a $b $paorb $d (λ pa, ∧Er $c $d ($pat pa))
      (λ pb, ∧Er $c $d ($pbt pb));
rule ∧Er $c $d (∃E $p $pexp ($c ∧ $d) $ppt) ↪
    ∃E $p $pexp $d (λ x pp, ∧Er $c $d ($ppt x pp));
rule ∧Er $a $b (nnpp ($a ∧ $b) $pnnab) ↪
  nnpp $b (λ h1 : ϵ (¬ $b), $pnnab
    (λ h2 : ϵ ($a ∧ $b), h1 (∧Er $a $b h2)));

rule ∃E $p (∃I $p $t $pt) _ $pxpxP ↪ $pxpxP $t $pt;
rule ∃E $p (∨E $a $b $paorb (∃ $p) $pat $pbt) $P $pxpP ↪
    ∨E $a $b $paorb $P (λ pa, ∃E $p ($pat pa) $P $pxpP)
                        (λ pb, ∃E $p ($pbt pb) $P $pxpP);
rule ∃E $p $pexp (_ ⇒ $d) $ppt $pc ↪
    ∃E $p $pexp $d (λ x pp, $ppt x pp $pc);
rule ∃E $p (∃E $q $pexp (∃ $p) $ppt) $P $pxpP ↪
    ∃E $q $pexp $P (λ x pp, ∃E $p ($ppt x pp) $P $pxpP);
rule ∃E $p $pexp (∀ (λ x, $b.[x])) $ppt $t ↪
    ∃E $p $pexp $b.[$t] (λ x pp, $ppt x pp $t);
rule ∃E $p (nnpp (∃ $p) $pnnep) $c $pptc ↪
  nnpp $c (λ h1 : ϵ (¬ $c), $pnnep
    (λ h2 : ϵ (∃ $p), h1 (∃E $p h2 $c $pptc)));

rule nnpp $c (∨E $a $b $paorb (¬ (¬ $c)) $pannc $pbnnc) ↪
    ∨E $a $b $paorb $c (λ pa, nnpp $c ($pannc pa))
      (λ pb, nnpp $c ($pbnnc pb));
rule nnpp $c (∃E $p $pexp (¬ (¬ $c)) $ppt) ↪
    ∃E $p $pexp $c (λ x pp, nnpp $c ($ppt x pp));
rule nnpp $p (nnpp (¬ (¬ $p)) $pnnnnp) ↪
  nnpp $p (λ pnp, $pnnnnp (λ pnnp, pnnp pnp));
rule nnpp (_ ⇒ $b) $pr $q ↪
  nnpp $b (λ h1, $pr (λ h2, h1 (h2 $q)));
rule nnpp (∀ $p) $pnnfp $t ↪
  nnpp ($p $t) (λ h1 : ϵ (¬ ($p $t)), $pnnfp
    (λ h2 : ϵ (∀ $p), h1 (h2 $t)));
rule nnpp $a.[] (λ h1, h1 (nnpp $a.[] (λ h2, $K.[h1;h2]))) ↪
  nnpp $a.[] (λ h1, $K.[h1;h1]);
rule nnpp _ (λ h1, h1 $K.[]) ↪ $K.[];
