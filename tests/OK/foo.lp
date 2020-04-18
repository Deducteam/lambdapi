constant symbol B : TYPE

constant symbol true  : B
constant symbol false : B

symbol neg : B → B

rule neg true  ↪ false
rule neg false ↪ true

constant symbol Prop : TYPE

injective symbol P : Prop → TYPE

constant symbol eq : B → B → Prop
constant symbol refl b : P (eq b b)

constant symbol case (p : B→Prop) : P (p true) → P (p false) → Πb, P b

theorem notK : Πb, P (eq (neg (neg b)) b)
proof
  assume b
  apply case (λb, eq (neg (neg b)) b)
  apply refl
  apply refl
qed
