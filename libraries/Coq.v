Definition imp (P Q: Prop) := P -> Q.
Definition all (A:Type) (P:A->Prop) := forall x:A, P x.
Axiom ind:Type.
