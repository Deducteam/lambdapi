// dk/lp symbols (on the right) the declarations of which are removed
// and whose uses are replaced by the given Coq expressions (on the left)

builtin "Type" ≔ hol.typ;
builtin "Prop" ≔ hol.bool;
builtin "coq.arr" ≔ hol.arr;
builtin "coq.imp" ≔ hol.imp;
builtin "coq.all" ≔ hol.forall;
builtin "@eq" ≔ hol.eq;
builtin "@eq_refl" ≔ hol.REFL;
