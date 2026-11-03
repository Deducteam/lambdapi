// example of quotient type

require open tests.OK.Nat tests.OK.Prod tests.OK.Quotient;

symbol intrel (p q:τ(nat × nat)) ≔ (p ₁) + (q ₂) = (q ₁) + (p ₂);

symbol refl_intrel p : π(intrel p p) ≔
begin
  reflexivity
end;

symbol int ≔ (nat × nat) ⫽ intrel;

symbol add (p q:τ(nat × nat)) ≔ ((p ₁) + (q ₁)) ‚ ((p ₂) + (q ₂));

opaque symbol add_compat:
  Π p p', π (intrel p p') → Π q q', π (intrel q q')
  → π (intrel (add p q) (add p' q')) ≔
begin
  assume p p' pp' q q' qq'; simplify;
  rewrite addnACA (p ₁) (q ₁) (p' ₂) (q' ₂); rewrite pp'; rewrite qq';
  rewrite addnACA (p' ₁) (q' ₁) (p ₂) (q ₂); reflexivity
end;

symbol class_add p q ≔ class intrel (add p q);

opaque symbol class_add_compat:
  Π p p', π (intrel p p') → Π q q', π (intrel q q')
  → π (class_add p q = class_add p' q') ≔
begin
  assume p p' pp' q q' qq'; simplify class_add; simplify rule off;
  apply sound intrel; refine add_compat p p' pp' q q' qq'
end;

symbol + ≔ lift2 intrel refl_intrel class_add class_add_compat;

require open tests.OK.FOL;

opaque symbol +_com a b: π (+ a b = + b a) ≔
begin
  refine ind_Quot (λ a, `∀ b, + a b = + b a) _; assume x;
  refine ind_Quot (λ b, + (class intrel x) b = + b (class intrel x)) _; assume y;
  apply sound; simplify; rewrite addnC (x ₁); rewrite addnC (y ₂); reflexivity
end;
