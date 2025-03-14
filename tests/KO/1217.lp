require open tests.OK.Set tests.OK.Prop tests.OK.FOL tests.OK.Eq tests.OK.HOL tests.OK.Impred tests.OK.PropExt;

symbol forallSimp (t : Set) (p : τ o) : π ((`∀ (x : τ t), p) = p) ≔
begin
    assume t p;
    refine propExt (`∀ x, p) p _ _
        {assume h; refine h (el t)}
        {assume h a; refine h}
end;

symbol a : τ o;
symbol b : τ ι → τ o;

symbol example : π ((`∀ x : τ ι, b x) ⇒ a) ≔
begin
  rewrite forallSimp;
  assume h; refine h
end;
