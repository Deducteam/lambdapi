constant symbol Prop : TYPE;
constant symbol true: Prop;

constant symbol ⩵ : Prop → Prop → Prop;
notation ⩵ infix 3.0;

symbol Trivial : Prop ≔ @true ⩵ true;
