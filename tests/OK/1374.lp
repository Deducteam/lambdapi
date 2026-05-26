require open tests.OK.HOL tests.OK.Tactic tests.OK.PropExt;

symbol #and ≔ (&);

symbol rem¬⊤ ≔ #and (#rewrite "" "" ¬⊤) (#rewrite "" "" ⊥∨);

symbol example x : π ((¬ ⊤ ∨ x) = x)≔
begin
    assume x;
    eval rem¬⊤;
    reflexivity
end;

symbol ¬⊤_noOp : π (¬ ⊤ = ⊥) ≔
begin
  refine propExt (¬ ⊤) ⊥ _ _
    {assume h1; refine h1 ⊤ᵢ}
    {assume h1; refine ⊥ₑ h1}
end;

symbol ⊥∨_noOp x : π ((⊥ ∨ x) = x) ≔
begin
  assume x; rewrite ∨_com; refine ∨⊥ x
end;

symbol example_noO_manual x : π ((¬ ⊤ ∨ x) = x)≔
begin
    assume x;
    rewrite ¬⊤_noOp;
    rewrite ⊥∨_noOp;
    reflexivity
end;

symbol rem¬⊤_noOP ≔ #and (#rewrite "" "" ¬⊤_noOp) (#rewrite "" "" ⊥∨_noOp);

symbol example_noOp x : π ((¬ ⊤ ∨ x) = x)≔
begin
    assume x;
    eval rem¬⊤_noOP;
    reflexivity
end;

symbol a: Prop;

symbol repeat_rewrite_defined ≔ #repeat (#rewrite "" "" =⊤);

symbol example1 : π ((a = ⊤) = a) ≔
begin
  eval repeat_rewrite_defined;
  reflexivity
end;

symbol example2 : π ((a = ⊤) = a) ≔
begin
  eval (#rewrite "" "" =⊤);
  reflexivity
end;

symbol example3 : π ((a = ⊤) = a) ≔
begin
  eval (#repeat (#rewrite "" "" =⊤));
  reflexivity
end;
