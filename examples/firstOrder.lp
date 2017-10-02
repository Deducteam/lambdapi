Term : Type.
Prop : Type.
prf  : Prop ⇒ Type.

true  : Prop.
false : Prop.

not : Prop ⇒ Prop.
and : Prop ⇒ Prop ⇒ Prop.
or  : Prop ⇒ Prop ⇒ Prop.
imp : Prop ⇒ Prop ⇒ Prop.

forall : (Term ⇒ Prop) ⇒ Prop.
exists : (Term ⇒ Prop) ⇒ Prop.

equals : Term ⇒ Term ⇒ Prop.

equiv : Prop ⇒ Prop ⇒ Prop.
[] equiv → λA:Prop. λB:Prop. and (imp A B) (imp B A).

tt : prf true.

[]    prf false → P:Prop ⇒ prf P.

[A]   prf (not A)      → prf A ⇒ prf false.

[A B] prf (and A B) → P:Prop ⇒ (prf A ⇒ prf B ⇒ prf P) ⇒ prf P.
[A B] prf (or  A B) → P:Prop ⇒ (prf A ⇒ prf P) ⇒ (prf B ⇒ prf P) ⇒ prf P.
[A B] prf (imp A B) → prf A ⇒ prf B.

[A] prf (forall A) → x:Term ⇒ prf (A x).
[A] prf (exists A) → P:Prop ⇒ (x:Term ⇒ prf (A x) ⇒ prf P) ⇒ prf P.

[x y] prf (equals x y) → P:(Term ⇒ Prop) ⇒ prf (P x) ⇒ prf (P y).

lem : A:Prop ⇒ prf (or A (not A)).

// *** Theorems

// implication 
// FIXME text right after comment does not work.

imp_elim : A:Prop ⇒ B:Prop ⇒ prf (imp A B) ⇒ prf A ⇒ prf B.
[] imp_elim → λA:Prop. λB:Prop. λp:(prf (imp A B)). p.

imp_intro : A:Prop ⇒ B:Prop ⇒ (prf A ⇒ prf B) ⇒ prf (imp A B).
[] imp_intro → λA:Prop. λB:Prop. λp:(prf A ⇒ prf B). p.

// disjunction

or_intro_1 : A:Prop ⇒ B:Prop ⇒ prf A ⇒ prf (or A B).
[] or_intro_1 → λA:Prop. λB:Prop. λp:prf A. λP:Prop.
                λf:(prf A ⇒ prf P). λg:(prf B ⇒ prf P). f p.

or_intro_2 : A:Prop ⇒ B:Prop ⇒ prf B ⇒ prf (or A B).
[] or_intro_2 → λA:Prop. λB:Prop. λp:prf B. λP:Prop.
                λf:(prf A ⇒ prf P). λg:(prf B ⇒ prf P). g p.

or_elim : A:Prop ⇒ B:Prop ⇒ prf (or A B) ⇒ C:Prop ⇒ prf (imp A C)
          ⇒ prf (imp B C)  ⇒ prf C.
[] or_elim → λA:Prop. λB:Prop. λp:prf (or A B). p.

// conjunction

and_intro  : A:Prop ⇒ B:Prop ⇒ prf A ⇒ prf B ⇒ prf (and A B).
[] and_intro → λA:Prop. λB:Prop. λa:prf A. λb:prf B. λP:Prop.
               λf:(prf A ⇒ prf B ⇒ prf P). f a b.

and_elim_1 : A:Prop ⇒ B:Prop ⇒ prf (and A B) ⇒ prf A.
[] and_elim_1 → λA:Prop. λB:Prop. λp:prf (and A B). p A (λa:prf A. λb:prf B. a).

and_elim_2 : A:Prop ⇒ B:Prop ⇒ prf (and A B) ⇒ prf B.
[] and_elim_2 → λA:Prop. λB:Prop. λp:prf (and A B). p B (λa:prf A. λb:prf B. b).

// Universal quantificator

forall_intro : P:(Term ⇒ Prop) ⇒ (t:Term ⇒ prf (P t)) ⇒ prf (forall P).
[] forall_intro → λP:(Term ⇒ Prop). λp:(t:Term ⇒ prf (P t)). p.

forall_elim : P:(Term ⇒ Prop) ⇒ t:Term ⇒ p:prf (forall P) ⇒ prf (P t).
[] forall_elim → λP:(Term ⇒ Prop). λt:Term. λp:prf (forall P). p t.

// Existential quantificator

exists_intro : P:(Term ⇒ Prop) ⇒ t:Term ⇒ prf (P t) ⇒ prf (exists P).
[] exists_intro → λP:(Term ⇒ Prop). λt:Term. λp:prf (P t). λA:Prop.
                  λf:(x:Term ⇒ prf (P x) ⇒ prf A). f t p.

exists_elim : P:(Term ⇒ Prop) ⇒ Q:Prop ⇒ prf (exists P)
              ⇒ prf (forall (λx:Term. imp (P x) Q)) ⇒ prf Q.
[] exists_elim → λP:(Term ⇒ Prop). λQ:Prop. λp1:prf (exists P).
                 λp2:prf (forall (λx:Term. imp (P x) Q)). p1 Q p2.

// Equality

eq_refl: prf (forall (λx:Term. equals x x)).
[] eq_refl → λx:Term. λP:(Term ⇒ Prop). λp:prf (P x). p.

eq_sym: prf (forall (λx:Term. forall (λy:Term. imp (equals x y) (equals y x)))).
[] eq_sym → λx:Term. λy:Term. λp:prf (equals x y).
            p (λz:Term. equals z x) (eq_refl x).

eq_trans: prf (forall (λx:Term. forall (λy:Term. forall (λz:Term.
            imp (and (equals x y) (equals y z)) (equals x z))))).
[] eq_trans → λx:Term. λy:Term. λz:Term.
              λp:prf (and (equals x y) (equals y z)).
              λP:(Term ⇒ Prop). λq:prf (P x).
              and_elim_2 (equals x y) (equals y z) p P
                (and_elim_1 (equals x y) (equals y z) p P q).
