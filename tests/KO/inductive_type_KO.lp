constant symbol Prop : TYPE;      // Type of propositions
injective symbol π : Prop → TYPE; // Interpretation of propositions in TYPE

set builtin "Prop"     ≔ Prop;
set builtin "P"     ≔ π;

symbol Nat : TYPE;

set debug +g;

symbol ind_plane : TYPE;
inductive plane : TYPE ≔
 | x0 : Nat → Nat → plane;

assert ⊢ ind_plane : Π (p : plane → Prop),
(Π z x1 : Nat, π (p (x0 z x1))) → Πx: plane, π (p x);

symbol pplane : plane → Prop;
symbol pix0 : Π z x1 : Nat, π (pplane (x0 z x1));
symbol n1 : Nat;
symbol n2 : Nat;
assert ⊢ ind_plane pplane pix0 (x0 n1 n2) ≡ pix0 n1 n2;
