Inductive type : Type :=
| bool : type
| ind : type
| arr : type -> type -> type.

Axiom Ind : Type.

Fixpoint _term B (t:type): Type :=
  match t with
  | bool => B
  | ind => Ind
  | arr a b => _term B a -> _term B b
  end.

#[bypass_check(positivity)]
Inductive _Prop : Type :=
| imp : _Prop -> _Prop -> _Prop
| _forall : forall a, (_term _Prop a -> _Prop) -> _Prop.

Definition term := _term _Prop.

Fixpoint proof (p:term bool) : Type :=
  match p with
  | imp x y => proof x -> proof y
  | _forall a q => forall x : term a, proof (q x)
  end.
