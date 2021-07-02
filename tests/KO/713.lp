symbol Type : TYPE;
injective symbol ε : Type → TYPE;

symbol = {T} (_ _ : ε T) : Type;
notation = infix 22;
symbol =_refl {T} (x : ε T) : ε (x = x);
symbol =_ind {T} (x y : ε T) : ε (x = y) → Π P, ε (P y) → ε (P x);

builtin "Prop"  ≔ Type;
builtin "P"     ≔ ε;
builtin "T"     ≔ ε;
builtin "eq"    ≔ =;
builtin "refl"  ≔ =_refl;
builtin "eqind" ≔ =_ind;

inductive ℕ : TYPE ≔
| O : ℕ
| S : ℕ → ℕ;

symbol nat : Type;
rule ε nat ↪ ℕ;

symbol succ x ≔ S x;

//flag "print_implicits" on;
//flag "print_domains" on;

symbol applyInd Q qO qS x :
  ε (ind_ℕ Q qO qS (succ x) =
     ind_ℕ Q qO qS (S x))
≔ begin
  assume Q qO qS x;

  have equality : ε (succ x = S x);
  reflexivity;

  //debug +turh;
  rewrite equality;
end;
