
require open tests.OK.HOL tests.OK.Tactic tests.OK.PropExt;

symbol #and ≔ (&);

// We can combine equality theorems from PropExt.lp to define tactics:

symbol rem¬⊤ ≔ #and (#rewrite "" "" ¬⊤) (#rewrite "" "" ⊥∨);

// We can use these as expected in proofs:

symbol example x : π ((¬ ⊤ ∨ x) = x)≔
begin
    assume x;
    eval rem¬⊤;
    reflexivity
end;

// However, if we state the same theories without the "opaque" modifier, like this:

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

// we can successfully use them manually to write a proof:

symbol example_noO_manual x : π ((¬ ⊤ ∨ x) = x)≔
begin
    assume x;
    rewrite ¬⊤_noOp;
    rewrite ⊥∨_noOp;
    reflexivity
end;

// But if we define an equivalent tactic using these theorems:

symbol rem¬⊤_noOP ≔ #and (#rewrite "" "" ¬⊤_noOp) (#rewrite "" "" ⊥∨_noOp);


// pattern matching fails:

symbol example_noOp x : π ((¬ ⊤ ∨ x) = x)≔
begin
    assume x;
    eval rem¬⊤_noOP;
    reflexivity
end;


