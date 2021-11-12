symbol Prop : TYPE;
symbol Type : TYPE;

injective symbol π : Prop → TYPE;

symbol ∀ [x : Prop] : (π x → Prop) → Prop;

rule π (∀ $f) ↪  Π w, π ($f w);

symbol ⊤ : Prop;
symbol top : π ⊤;

symbol ⊥ : Prop;

symbol ⇒ A B ≔ @∀ A (λ _, B); notation ⇒ infix right 14;

symbol bool : TYPE;
symbol true : bool;
symbol false : bool;

symbol if : Prop → Prop → bool → Prop;

rule if $vt _   true  ↪ $vt
with if _   $vf false ↪ $vf;

symbol is_true ≔ if ⊤ ⊥;

symbol test b : π (is_true b ⇒ ⊤)
≔ begin
  assume b H;
  refine top;
end;
