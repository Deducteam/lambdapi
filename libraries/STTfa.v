Inductive _Set : Type :=
| prop : _Set
| ind : _Set
| arr : _Set -> _Set -> _Set.

Axiom Ind : Type.

Fixpoint _El B (t:_Set): Type :=
  match t with
  | prop => B
  | ind => Ind
  | arr u v => _El B u -> _El B v
  end.

#[bypass_check(positivity)]
Inductive _Prop : Type :=
| imp : _Prop -> _Prop -> _Prop
| all : forall a, (_El _Prop a -> _Prop) -> _Prop.

Definition El := _El _Prop.

Fixpoint Prf (p:El prop) : Type :=
  match p with
  | imp x y => Prf x -> Prf y
  | all a q => forall x : El a, Prf (q x)
  end.

