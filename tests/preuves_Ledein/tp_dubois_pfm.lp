// Cours et exercices de la découverte de lambdapi
// Inspiré de la version Coq de Catherine Dubois
// (elle-même inspirée de Software Foundations)

// Tout ce qui est en commentaire est du Coq qui compile.
// Ma traduction vers LP suit.

require open tests.preuves_Ledein.notation
                                  
////////////////////////////////////
// Avant de prendre la route...
////////////////////////////////////
                                  
// Inductive route : Type :=
// | departementale : route
// | nationale : route
// | autoroute : route.

constant symbol route          : Set
definition R ≔ τ route
constant symbol departementale : R
constant symbol nationale      : R
constant symbol autoroute      : R

// Definition agrandir (r : route) := 
//   match r with
//  | departementale => nationale
//  | nationale => autoroute
//  | autoroute => autoroute
//  end.
                                 
symbol agrandir : R ⇒ R
rule agrandir departementale → nationale
 and agrandir nationale      → autoroute
 and agrandir autoroute      → autoroute

// Eval compute in (agrandir (agrandir nationale)).
compute (agrandir (agrandir nationale))                           

theorem agrandir_test : // version théorème 
  π (eq {route} (agrandir (agrandir nationale)) autoroute)
proof
  refine eq_refl autoroute
qed

//Inductive terrain : Type :=
//| t_terre : terrain
//| t_route : route -> terrain
//| t_batiment : terrain.

constant symbol terrain    : Set
definition Ter ≔ τ terrain
constant symbol t_terre    : Ter
constant symbol t_route    : R ⇒ Ter
constant symbol t_batiment : Ter

//Check (t_route nationale).
type (t_route nationale)

/////////////////////////////
// Exercice 1.
/////////////////////////////

// ///////////////////////// Booléen

//Check true.
type true

//Print bool.
// ??

//Definition negb b :=
//  match b with
//  | true => false
//  | false => true
//  end.

symbol negb : B ⇒ B
rule negb true → false
 and negb false → true

// Definition andb b1 b2 :=
//  match b1 with
//  | true => b2
//  | false => false
//  end.
                  
symbol andb : B ⇒ B ⇒ B
rule andb false _  → false
 and andb _ false  → false
 and andb &b1 true → &b1
 and andb true &b2 → &b2

// Definition orb b1 b2 :=
//   match b1 with
//   | true => true
//   | false => b2
//   end.

symbol orb : B ⇒ B ⇒ B
rule orb true _  → true
 and orb _ true  → true
 and orb &b1 false → &b1
 and orb false &b2 → &b2

// /////////////////////// Entiers naturels
                  
// Inductive nat : Type :=
// | O : nat
// | S : nat -> nat.

//Cf notation.lp

// Check O.
type O
// Check S. 
type S

//Notation "0" := O.
//Notation "1" := (S O).
     
//Cf notation.lp
     
//Fixpoint plus n m :=
//  match n with
//  | 0 => m
//  | S n' => S (plus n' m)
//  end.
     
symbol plus : N ⇒ N ⇒ N
rule plus 0      &m → &m
 and plus (S &v) &m → S (plus &v &m)

// Notation "n + m" := (plus n m).
set declared "+"
set infix right 6 "+" ≔ plus

// Eval compute in (0 + 1).
compute 0+1
                        
// Eval compute in (plus 1 1).
compute plus 1 1

// ///////////////////////////// Liste de booléens

// Inductive list_bool : Type :=
// | nilb : list_bool
// | consb : bool -> list_bool -> list_bool.

constant symbol list_bool : Set
definition Lb ≔ τ list_bool    // équivalent à ce qui a été fait avant o:-)
constant symbol nilb  : Lb
constant symbol consb : B ⇒ Lb ⇒ Lb

// Check nilb.
type nilb

//Definition example := consb true (consb false (consb true nilb)).
definition example ≔ consb true (consb false (consb true nilb))

//Check example.
type example

// Fixpoint appb l1 l2 :=
//   match l1 with
//   | nilb => l2
//   | consb a l => consb a (appb l l2)
//  end. 

symbol appb : Lb ⇒ Lb ⇒ Lb
rule appb nilb         &l2 → &l2
 and appb (consb &a &l) &l2 → consb &a (appb &l &l2)

// Check appb.
type appb

// ///////////////////////////////////// Suite booléen
     
//Definition apply_neg (f : _ -> _ -> bool) b1 b2 :=
//  f (negb b1) (negb b2).
definition apply_neg (f: _ ⇒ _ ⇒ B) b1 b2 ≔ f (negb b1) (negb b2)

// Check apply_neg.
type apply_neg

// Definition nor := apply_neg andb. @TODO_1
// definition nor : B ⇒ B ⇒ B  ≔ apply_neg andb    // non
// definition nor a b ≔ apply_neg andb a b         // non
// definition nor (a:B) (b:B) ≔ apply_neg andb a b // non
                             
// Check nor.
// type nor
 
// Definition norb := 
//   apply_neg (fun b1 => fun b2 => b2).
definition norb ≔ apply_neg (λb1, λb2, b2)
 
// Eval compute in (norb true false).
compute (norb true false)

// Definition idb : bool -> bool := fun b => b.
definition idb : B ⇒ B ≔ λb, b

//(* identique à
//Definition idb (b : bool) := b. *)
definition idb_bis b:B ≔ b
                             
//Definition my_first := apply_neg (fun b1 => fun b2 => b1).
definition my_first ≔ apply_neg (λb1, λb2, b1)
                         
//Eval compute in (my_first true false).
compute (my_first true false)

// ////////////////////////////////// Liste polymorphe

// Inductive list (A:Type) : Type :=
// | nil : list A
// | cons : A -> list A -> list A .

// Traduction de manière stricte :
// constant symbol list : Set ⇒ Set
// definition L a ≔ τ (list a)
// constant symbol nil a : L a
// constant symbol cons a : τ a ⇒ L a ⇒ L a

// Mais j'allège un peu :
constant symbol list : Set ⇒ Set
definition L a ≔ τ (list a)
constant symbol nil {a} : L a
constant symbol cons {a} : τ a ⇒ L a ⇒ L a
                       
// Eval compute in (cons nat 1 (cons nat (S 1) (nil nat))).
compute (cons {nat} 1 (cons {nat} (S 1) (nil {nat})))

// Eval compute in (cons bool true (cons bool false (nil bool))).
compute (cons {bool} true (cons {bool} false (nil {bool})))
					    
// Definition id (A:Type) (x:A) := x.
definition id A x:A ≔ x

// Fixpoint length (A:Type) (l:list A) :=
//  match l with
//  | nil _ => 0
//  | cons _ _ t => S (length A t)
//  end. 

symbol length A : L A ⇒ N
rule length _ (nil _) → 0
 and length &A (cons _ _ &t) → &t
                      
//Eval compute in (length bool 
//   (cons bool true 
//         (cons bool false (nil bool)))).
compute (length bool (cons {bool} true
                            (cons {bool} false (nil {bool}))))

//Fixpoint app (A:Type) l1 l2 :=
//  match l1 with
//  | nil _ => l2
//  | cons _ a l => cons A a (app A l l2)
//    end. 
symbol app A : L A ⇒ L A ⇒ L A
rule app _ (nil _) &l2        → &l2
 and app &A (cons {&A} &a &l) &l2 → cons {&A} &a (app &A &l &l2)

//Definition apply_neg_gen (A:Type) (f:_->_->A) b1 b2 :=
//  f (negb b1) (negb b2).
definition apply_neg_gen A (f : _ ⇒ _ ⇒ A) b1 b2 ≔
    f (negb b1) (negb b2)

// Definition nor2 := apply_neg_gen bool  andb.
// definition nor2 ≔ apply_neg_gen bool andb
// @TODO_2 ( // @TODO_1)

// Definition apply_neg_gen2 {A:Type} (f:_->_->A) b1 b2 :=
//  f (negb b1) (negb b2).
definition apply_neg_gen2 {A} (f : _ ⇒ _ ⇒ A) b1 b2 ≔
f (negb b1) (negb b2)

// Definition nor3 := apply_neg_gen2 andb.
// definition nor3 ≔ apply_neg_gen andb
// @TODO_3 ( // @TODO_1)

// Definition toto (b1 b2 : bool) := 0. 
definition toto (b1 b2 : B) ≔ 0

// Eval compute in apply_neg_gen  nat toto true false.
compute apply_neg_gen N toto true false
                                       
// //////////////////////////////////////////// Logique sur les booléens

require open tests.preuves_Ledein.Logic
definition equiv (A B : Prop) ≔ (imp A B) ∧ (imp B A)
set infix left 7 "⇔" ≔ equiv
                       
// Check True. (* True : Prop *)
type true // (* true : B *)                                      

// Check True -> False. (* True -> False : Prop *)
// type ??

// Lemma bool_trivial : forall (P : bool -> Prop) b, P b -> P b.
// Admitted.
theorem bool_trivial : ∀(P:B ⇒ Prop) b, π (P b) ⇒ π (P b)
// Note : Check (_ ⇒ _) donne TYPE ⇒ TYPE
proof
  assume P b H
  apply H
qed

// Induction principle on B.
symbol bool_ind : ∀(P:B⇒Prop), π(P true) ⇒ π(P false) ⇒ ∀b, π(P b)

//Lemma bool_ext : forall (P : bool -> Prop), P true /\ P false ->
//  forall b, P b.
//Admitted.
theorem bool_ext :
∀P : B ⇒ Prop, π ((P true) ∧ (P false)) ⇒ ∀b, π(P b)
proof
  assume P Hp b
  refine bool_ind (λz, P z) _ _ _               
  apply and_elim_left _ (P false)
  refine Hp
  apply and_elim_right (P true) _
  apply Hp
qed

//Lemma bool_ext2 : forall (P : bool -> Prop), P true -> P false ->
//  forall b, P b.
//Admitted.
theorem bool_ext2 :
∀P : B ⇒ Prop, π (P true) ⇒ π (P false) ⇒ ∀b, π (P b)
proof
  assume P HPT HPF b
  refine bool_ind (λz, P z) _ _ _
  apply HPT
  apply HPF
qed

//(** Preuve *)
//
//Lemma andb_prop : forall b1 b2,
//  andb b1 b2 = true -> b1 = true /\ b2 = true.
//Proof.
//  intros b1 b2 H. 
//  (* introduit les hypothèses *)
//  split. (* sépare le but en deux sous-buts *)
//  - destruct b1. (* raisonnement par cas *)
//    + reflexivity. (* true = true *)
//    + simpl in H. discriminate H. (* false <> true *)
//  - destruct b2. (* raisonnement par cas *)
//    + reflexivity. (* true = true *)
//    + destruct b1 .  (* raisonnement par cas *)
//      * simpl in H. discriminate H. (* false <> true *)
//      * simpl in H. discriminate H. (* false <> true *)
//Qed.
//set declared "<>"
//definition diff a b ≔ ¬(eq a b)
//set infix left 6 <> ≔ diff
 

theorem discr : π (eq {bool} false true) ⇒ π ⊥                             //  @TODO_4_admit
proof
  assume H
  apply not_elim (eq {bool} false true)
  // Case π (¬ (eq false true))
  //assume Hbis
  // Case π (eq false true)
  //apply H
admit

//theorem andb_prop :                        // Il me manque un outil pour y arriver avec cet énoncé
//∀b1 b2, π (eq {bool} (andb b1 b2) true) ⇒
//                    π ((eq {bool} b1 true) ∧ (eq {bool} b2 true))
theorem andb_prop : ∀b1 b2, π (imp (eq {bool} (andb b1 b2) true) ((eq {bool} b1 true) ∧ (eq {bool} b2 true) ))
proof
  assume b1 b2
  refine bool_ind (λz, imp (eq {bool} (andb z b2) true) ((eq {bool} z true) ∧ (eq {bool} b2 true)) ) _ _ _
  // Case b1 = true                                            
  simpl
  apply imp_intro assume H
  apply and_intro
  reflexivity
  apply H
  // Case b1 = false
  simpl
  apply imp_intro assume H
  apply false_elim (eq {bool} false true ∧ eq {bool} b2 true)
  apply discr apply H
qed

////////////////////////////////////
//(** Exercice 2 *)
/////////////////////////////////////
//(*
//   [andb_true_iff : forall b1 b2, andb b1 b2 = true <-> b1 = true /\ b2 = true]
//    Montrer [orb_true_iff], un résultat similaire sur [orb].  
// *)

theorem andb_true_iff : ∀b1 b2, π ((eq {bool} (andb b1 b2) true) ⇔ (eq {bool} b1 true ∧ eq {bool} b2 true))
proof
  assume b1 b2
  refine bool_ind (λz, imp (eq (andb z b2) true)
                           (eq z true ∧ eq b2 true) ∧
                       imp (eq z true ∧ eq b2 true)
                           (eq (andb z b2) true)) _ _ _
  // Case b1 = true
  simpl
  apply and_intro
    apply imp_intro assume H apply and_intro
      reflexivity
      apply H
    apply imp_intro assume H apply and_elim_right (eq {bool} true true) apply H
  // Case b1 = false
  simpl
  apply and_intro
    apply imp_intro assume H
      apply false_elim (eq {bool} false true ∧ eq {bool} b2 true)
      apply discr apply H
  apply imp_intro assume H apply and_elim_left _ (eq {bool} b2 true) apply H
qed

theorem orb_true_iff : ∀b1 b2, π ((eq {bool} (orb b1 b2) true) ⇔ (eq {bool} b1 true ∨ eq {bool} b2 true))
proof
  assume b1 b2
  refine bool_ind (λz, imp (eq (orb z b2) true)
                           (eq z true ∨ eq b2 true) ∧
                       imp (eq z true ∨ eq b2 true)
                           (eq (orb z b2) true)) _ _ _
  // Case b1 = true
  simpl
  apply and_intro
    apply imp_intro assume H apply or_intro_left apply H
    apply imp_intro assume H reflexivity
  // Case b1 = false
  simpl
  apply and_intro
    apply imp_intro assume H apply or_intro_right apply H
    apply imp_intro assume H apply or_elim (eq {bool} false true) (eq {bool} b2 true) (eq {bool} b2 true) apply H
      assume Hfalse apply false_elim (eq {bool} b2 true) apply discr apply Hfalse
      assume H2 apply H2
qed

// //////////////////////////////////////////// Retour sur les entiers naturels

//Lemma plus_0_n : forall n, 0 + n = n.
//Proof.
//intro n. simpl. reflexivity.
//Qed.
theorem plus_0_n : ∀n, π (eq {nat} (plus O n) n)
proof
  assume n
  refine eq_refl n
qed

// Induction principle
symbol nat_ind P : π (P 0) ⇒ (∀x, π (P x) ⇒ π (P (S x))) ⇒ ∀x, π (P x)

// Injective principle
symbol nat_inj : ∀n m, π (eq {nat} (S n) (S m)) ⇒ π (eq {nat} n m)  // A voir !

//Lemma plus_n_0 : forall n, n + O = n.
//Proof.
//induction n.
//+  simpl. reflexivity.
//+ simpl. rewrite IHn. reflexivity.
//Qed.
theorem plus_n_0 : ∀n, π (eq {nat} (plus n O) n)
proof
  assume n
  refine nat_ind (λz, eq (plus z O) z) _ _ _
  // Case n = O
  refine eq_refl O
  // Case = S n'
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity    
qed

//Fixpoint mult (n m : nat) :  nat :=
//  match n with
//  | O => 0
//  | S n' => m + (mult n' m)
//  end.
symbol mult : N ⇒ N ⇒ N
rule mult O _ → 0
 and mult (S &v) &m → plus &m (mult &v &m)

//Notation "n * m" := (mult n m).
set infix left 6 "*" ≔ mult

//Lemma mult_0_n : forall n : nat, 0*n=0.
//Proof.
//intros. simpl. reflexivity.
//Qed.
theorem mult_0_n : ∀n, π (eq {nat} (0*n) 0)
proof
  assume n
  refine eq_refl O
qed

//Lemma mult_n_0 : forall n, n*0= 0.
//Proof.
//induction n.
//+  apply mult_0_n.
//+  simpl. exact IHn.
// (* ou assumption*)
//Qed.
theorem mult_n_0 : ∀n, π (eq {nat} (n*0) 0)
proof
  assume n
  refine nat_ind (λz, eq {nat} (z*0) 0) _ _ n
  // Case n = O
  refine eq_refl O
  // Case = S n'
  assume n' Hn'
  simpl
  apply Hn'
qed

//Lemma plus_assoc : forall n m p,
//  n+(m+p) = n+m+p.
//Proof.
//induction n ; intros m p.
//+ simpl. reflexivity. 
//+ simpl. rewrite IHn. reflexivity.
//Qed.
theorem plus_assoc :
//∀(n m p:N), π (eq {nat} (n+(m+p)) (n+m+p))
∀(n m p:N), π (eq {nat} (plus n (plus m p)) (plus (plus n m) p))
proof
  assume n m p
  //refine nat_ind (λz, eq {nat} (z+(m+p)) (z+m+p)) _ _ n
  refine nat_ind (λz, eq {nat} (plus z (plus m p)) (plus (plus z m) p)) _ _ n
  reflexivity
  assume n' Hn'
  simpl
  rewrite Hn'
  reflexivity
qed

//Lemma plus_n_Sm : forall n m,
//  n + S m = S (n + m).
//Proof.
//induction n ; intro m ; simpl.
//+ reflexivity.
//+ rewrite IHn. reflexivity.
//Qed.
theorem plus_n_Sm : ∀n m, π (eq {nat} (plus n (S m)) (S (plus n m)))
proof
  assume n m
  refine nat_ind (λz, (eq {nat} (plus z (S m)) (S (plus z m)))) _ _ n
  reflexivity
  simpl
  assume n' Hn'
  rewrite Hn'
  reflexivity
qed

//Lemma plus_comm : forall n m, n+m=m+n.
//Proof.
//induction n ; intros m0.
//+ simpl. rewrite plus_n_0. reflexivity.
//+ simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
//Qed.
theorem plus_comm : ∀n m, π( eq {nat} (plus n m) (plus m n))
proof
  assume n m
  refine nat_ind (λz, (eq {nat} (plus z m) (plus m z))) _ _ n
    simpl rewrite plus_n_0 reflexivity
    simpl assume n' Hn' rewrite Hn' rewrite plus_n_Sm reflexivity
qed

//Lemma mult_n_Sm : forall n m, n*S m=n+n*m.
//Proof.
//induction n ; intros m0 ; simpl.
//+ reflexivity.
//+ rewrite IHn.
//  do 2 (rewrite plus_assoc).
//  rewrite plus_comm with (n:=n) (m := m0). reflexivity.
//Qed.
//theorem mult_n_Sm : ∀n m, π (eq {nat} (n*S m) (n+n*m))
theorem mult_n_Sm : ∀n m, π (eq {nat} (mult n (S m)) (plus n (mult n m)))
proof
  assume n m
  refine nat_ind (λz, (eq {nat} (mult z (S m)) (plus z (mult z m)))) _ _ n
    reflexivity
    assume n' Hn' simpl rewrite Hn'
    rewrite plus_assoc rewrite plus_assoc rewrite plus_comm n' m reflexivity
qed

//Lemma mult_comm : forall n m, n *m=m*n.
//Proof.
//induction n ; intros m0 ; simpl.
//+ rewrite mult_n_0. reflexivity.
//+ rewrite IHn. rewrite mult_n_Sm.  reflexivity.
//Qed.
theorem mult_comm : ∀n m, π (eq {nat} (mult n m) (mult m n))
proof
  assume n m
  refine nat_ind (λz, (eq {nat} (mult z m) (mult m z))) _ _ n
    rewrite mult_n_0 reflexivity
    assume n' Hn' simpl rewrite Hn'
    rewrite mult_n_Sm reflexivity
qed

//Lemma mult_plus_distr_r : forall n m p,
//  (n+m)*p = n*p+m*p.
//Proof.
//induction n ; intros m p; simpl.
//+ reflexivity.
//+ rewrite IHn. apply plus_assoc.
//Qed.
theorem mult_plus_distr_r :
∀n m p, π (eq {nat} (mult (plus n m) p) (plus (mult n p) (mult m p)))
proof
  assume n m p
  refine nat_ind (λz, (eq {nat} (mult (plus z m) p) (plus (mult z p) (mult m p)))) _ _ n
    reflexivity
    assume n' Hn' simpl rewrite Hn'
    apply plus_assoc p (mult n' p) (mult m p) // pas inféré
qed

//Lemma mult_assoc : forall n m p, n*(m*p) = (n*m)*p.
//Proof.
//induction n ; intros m p; simpl.
//+ reflexivity.
//+ rewrite IHn. rewrite mult_plus_distr_r. reflexivity. 
//Qed.
theorem mult_assoc : ∀ n m p, π (eq {nat} (n*(m*p)) ((n*m)*p))
proof
  assume n m p
  refine nat_ind (λz, (eq {nat} (z*(m*p)) ((z*m)*p))) _ _ n
    reflexivity
    simpl assume n' Hn' // simpl
    rewrite Hn'
    rewrite mult_plus_distr_r // m (mult n' m) p
    reflexivity
qed

//* Prouver directement *)
//Lemma mult_plus_distr_l : forall n m p,
//  n*(m+p)=n*m+n*p.
//Proof.
//induction n; intros m p ; simpl.
//+ reflexivity.
//+ rewrite IHn. 
//    rewrite plus_comm with (n:=p) (m:=n*p).
//    rewrite <- plus_assoc with (n:=m) (m:=n*m) (p:=n*p+p).
//    rewrite plus_comm with (n:=m) (m:=n*m + (n*p + p)).
//    do 2 (rewrite plus_assoc).
//    rewrite plus_comm with (n:=m) (m:=p).
//    rewrite <- plus_assoc with (n:=p + m) (m:=n*m) (p:=n*p).
//    rewrite plus_comm with (n:=p + m) (m:=n*m + n*p).
//    rewrite plus_assoc. reflexivity.
//Qed.
theorem mult_plus_distr_l :
∀n m p, π (eq {nat} (mult n (plus m p)) (plus (mult n m) (mult n p)))
proof
  assume n m p
  refine nat_ind (λz, eq {nat} (mult z (plus m p))
                               (plus (mult z m) (mult z p))) _ _ n
  reflexivity
  simpl assume n' IHn' rewrite IHn'
  rewrite plus_comm p (n'*p)
  symmetry
  rewrite plus_assoc m (mult n' m) (plus (mult n' p) p)
  //symmetry
  //rewrite plus_comm p (n'*p)
  //symmetry
  //rewrite plus_comm m (plus (mult n' m) (plus (mult n' p) p))
  //rewrite plus_assoc rewrite plus_assoc
  //rewrite plus_comm m p
  //rewrite <- plus_assoc (p + m) (n*m) (n*p)
  //rewrite plus_comm (p + m) (n*m + n*p)
  //rewrite plus_assoc reflexivity
qed // @TODO_5

// 
//(* Prouver en utilisant les lemmes precedents
//   (mais bien sur pas [mult_plus_distr_l]) *)
//Lemma mult_plus_distr_l_bis : forall n m p,
//  n*(m+p)=n*m+n*p.
//Proof.
//intros n m p.
//rewrite mult_comm with (n := n) (m := m).
//rewrite mult_comm with (n := n) (m := p).
//rewrite <- mult_plus_distr_r.
//apply mult_comm.
//Qed.
theorem mult_plus_distr_l_bis : ∀n m p, π (eq {nat} (mult n (plus m p)) (plus (mult n m) (mult n p)))
proof
  assume n m p
  rewrite mult_comm n m
  rewrite mult_comm n p 
  //rewrite mult_plus_distr_r
  //apply mult_comm
admit // @TODO_6

////////////////////////////
//  Exercice 3. Un peu de logique !
////////////////////////////

//Lemma impl_and : forall P Q R : Prop, (P->Q->R) -> (P /\ Q -> R).
//Proof.
//intros P Q R Hyp1 Hyp2.
//destruct Hyp2 as [Hp Hq].
//apply Hyp1 ; assumption.
//Qed.
theorem impl_and : ∀P Q R : Prop, (π P ⇒ π Q ⇒ π R) ⇒ (π(P ∧ Q) ⇒ π R)
proof
  assume P Q R Himp Hand
  apply Himp
  apply and_elim_left P Q
  apply Hand
  apply and_elim_right P Q
  apply Hand     
qed

//Lemma and_impl : forall P Q R : Prop, (P /\ Q -> R) -> (P -> Q -> R).
//Proof.
//intros P Q R Hyp1 H1 H2.
//apply Hyp1.
//split ; assumption.
//Qed.
theorem and_impl_fl : ∀P Q R : Prop, (π (P ∧ Q) ⇒ π R) ⇒ (π P ⇒ π Q ⇒ π R)
proof
  assume P Q R Hand HP HQ
  apply Hand
  apply and_intro
  apply HP
  apply HQ 
qed
theorem and_impl : ∀P Q R : Prop, π (imp (imp (P ∧ Q) R) (imp P (imp Q R)))
proof
  assume P Q R
  apply imp_intro assume Hand
  apply imp_intro assume P
  apply imp_intro assume Q                     
  //apply and_intro P Q
  //apply HP
  //apply HQ 
admit // @TODO_7 problème ?
      
//Lemma and_impl_iff : forall P Q R : Prop, (P /\ Q -> R) <-> (P -> Q -> R).
//Proof.
//split.
//+ apply and_impl.
//+ apply impl_and.
//Qed.
theorem and_impl_iff : ∀P Q R : Prop,
π ((imp (P ∧ Q) R) ⇔ (imp P (imp Q R)))  
proof
  assume P Q R
  apply and_intro
  simpl
  //apply imp_intro
  //rewrite imp_intro
  apply and_impl
  apply impl_and P Q
admit // @TODO_8 problème ?

//Lemma impl_not : forall P : Prop, P -> ~ ~ P.
//Proof.
//intros P Hyp.
//unfold not.
//intro Hyp1.
//apply Hyp1.
//assumption.
//Qed.
theorem impl_not : ∀P : Prop, π P ⇒ π (¬ (¬ P))
proof
  assume P HP
  apply not_intro (¬ P)
  assume HnotP
  apply not_elim P
  apply HnotP
  apply HP
qed

//Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
//Proof.
//intros P Q H1 H2.
//apply H2.
//assumption.
//Qed.
theorem modus_ponens : ∀P Q : Prop, π P ⇒ (π P ⇒ π Q) ⇒ π Q
proof
  assume P Q HP Himp
  apply Himp
  apply HP
qed

//(* en utilisant [modus_ponens] *)
//Lemma impl_not_bis : forall P : Prop, P -> ~ ~ P.
//Proof.
//intro P. unfold not.
//apply modus_ponens.
//Qed.
theorem impl_not_bis : ∀P : Prop, π P ⇒ π (¬ (¬ P))
proof
  assume P HP                       // je n'ai pas utilisé modus_ponens...
  apply not_intro (¬P)
  assume HnotP
  apply not_elim P
    apply HnotP
    apply HP
  //refine [π (¬ (¬ P))] not_intro (¬P)
  //refine (λz, π P ⇒ π z) not_intro (¬P)
  // rewrite not_intro (¬P)
  //rewrite (¬ (¬ P)) as H
  //                     ((P ⇒ ⊥) ⇒ ⊥)
  //apply modus_ponens P ⊥
qed

//(* a partir de [impl_not] *)
//Lemma P_notP_contradiction : forall P : Prop, ~ (P /\ ~ P).
//Proof.
//intro P.
//unfold not .
//(*apply impl_and.
//apply modus_ponens.*)
//intro H1.
//destruct H1 as [HH1 HH2].
//apply HH2. assumption.
//Qed.
theorem P_notP_contradiction : ∀P : Prop, π (¬(P ∧ ¬P))
proof
  assume P
  apply not_intro (P ∧ ¬P)
  assume Hand
  apply not_elim P
     apply and_elim_right P _   apply Hand
     apply and_elim_left _ (¬P) apply Hand
qed

//Lemma not_and : forall P Q : Prop, P \/ Q -> ~(~ P /\ ~Q).
//Proof.
//Admitted.
theorem not_and : ∀P Q : Prop, π (P ∨ Q) ⇒ π (¬(¬P ∧ ¬Q))
proof
  assume P Q Hor
  apply not_intro (¬P ∧ ¬Q)
  assume Hand
  refine or_elim P Q ⊥ _ _ _
  // Case π (P ∨ Q)
  apply Hor
  // Case π P ⇒ π ⊥
  assume HP apply not_elim P
      refine and_elim_left (¬P) (¬Q) _ apply Hand
      apply HP
  // Case π Q ⇒ π ⊥
  assume HQ apply not_elim Q
     refine and_elim_right (¬P) (¬Q) _ apply Hand
     apply HQ
qed

//Lemma exists_not_forall : forall P : nat -> Prop, 
//(exists n, P n) ->  ~(forall n,~ (P n)).
//Proof.
//intros P H H1. 
//destruct H as [n0 H0].
//specialize (H1 n0).
//contradiction.
//Qed.
//theorem exists_not_forall : ∀(P : N ⇒ Prop), (∃n, π(P n)) ⇒ π (¬(∀m, π (¬ (P m)))))
//proof
//qed
//@TODO_

////////////////////////
//  Exercice 4 - Liste polymorphe (Cf avant)
////////////////////////

//Check list.
// ??

//Notation "[]" := nil.

//Notation "[ x ]" := (cons x nil).

//Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
// possible ?

//(* Montrer que le nombre d'éléments de la concaténation de deux listes est la somme
//	des nombres des éléments de chacune *)

theorem sum_length : ∀A (l1 l2 : L A), π (eq {nat} (plus (length A l1) (length A l2)) (length A (app A l1 l2)))
proof
  assume A l1 l2
  
qed

//(* Definir la fonction qui renverse une liste (on utilisera la fonction précédente app)
// et  montrer que reverse(reverse l) = l pour tout l, par induction sur l*)
symbol reverse A : L A
rule reverse nil          → nil
 and reverse (cons &v &q) → app (reverse &q) (cons &v nil)

theorem fixpoint_reverse : ∀l, reverse(reverse l) = l
proof
qed

//////////////////////////
//(** Exercice 5 *)
//////////////////////////
//
//Definition is_even n := exists p, n = 2 * p.
//
//Lemma zero_is_even : is_even 0.
//Proof.
//unfold is_even.
//exists 0. simpl. reflexivity.
//Defined.
//
//
//Lemma is_even_plus : forall n p, 
//   is_even n -> is_even p -> is_even (n + p).
//Proof.
//intros n p Hn Hp.
//unfold is_even in Hn.
//destruct Hn as [k Hk].
//destruct Hp as [t Ht].
//unfold is_even.
//exists (k + t).
//rewrite  mult_plus_distr_l.
//rewrite Hk.  rewrite Ht. reflexivity.
//Qed.       
//
///////////////////////////
//(** * Exercice 5. *)
///////////////////////////
//
//(** On rappelle la dÃ©finition de [even] sous forme d'un predicat inductif . *)
//
//Inductive even : nat -> Prop :=
//| even_0 : even 0
//| even_SS : forall n, even n -> even (S (S n)).
//
//
//Lemma even_4 : even 4.
//Proof.
//apply even_SS. apply even_SS. apply even_0.
//Qed.
//
//(* ou avec une syntaxe fonctionnelle*)
//Theorem even_4' : even 4.
//Proof. exact (even_SS 2 (even_SS 0 even_0)).
//Qed.
//
//Theorem even_plus4 : forall n, even n -> even (4 + n).
//Proof.
//  intros n. simpl. intros Hn.
//  apply even_SS. apply even_SS. assumption.
//Qed.
//
//Theorem ev_minus2 : forall n,
//  even n -> even (pred (pred n)).
//Proof.
//  intros n H.
//  inversion H  as [| p Hp].
//  - (* H = even_0 *) simpl. apply even_0.
//  - (* H = even_SS p Hp *) simpl. exact Hp (* ou assumption*).
//Qed.
//
//Theorem even5_nonsense :
//  even 5 -> 2 + 2 = 9.
//Proof.
//  intro H.
//  inversion H. 
//  inversion H1.
//  inversion H3.
//Qed.
//
//Lemma ev_even : forall n,
//  even n -> exists k, n = 2 * k.
//Proof.
//  intros n E.
//  induction E as [|k Hk IH].
//  - (* E = even_0 *)
//    exists 0. reflexivity.
//  - (* E = even_SS k Hk
//       with IH : exists k', n' = double k' *)
//    destruct IH as [k' Hk'].
//    rewrite Hk'. exists (S k'). simpl.
//    Search plus.
//    rewrite <- plus_n_Sm.
//    replace (k' + 0) with k'. reflexivity.
//    apply plus_n_O.
//Qed.
//(** Prouver les lemmes suivants. *)
//
//Lemma even_n_or_Sn : forall n, even n \/ even (S n).
//Proof.
//Admitted.
//
//Lemma even_n_not_Sn : forall n, even n -> ~ even (S n).
//Proof.
//Admitted.
//
//Lemma even_dec : forall n, even n \/ ~ even n.
//Proof.
//Admitted.
//
//(** Induction de 2 en 2. *)
//Lemma two_steps_induction : forall P : nat -> Prop, P 0 -> P 1 ->
//  (forall n, P n -> P (S (S n))) ->
//  forall n, P n.
//Proof.
//  intros P H0 H1 IHn.
//  assert (forall n, P n /\ P (S n)) as Hn.
//Admitted.
//
//(** DÃ©finir [evenb : nat -> bool] qui teste si un entier est pair. *)
//
//Fixpoint evenb (n:nat) : bool.
//Admitted.
//
//(** Prouver les lemmes suivants. Si vous avez besoin de rÃ©sultats sur les
//    boolÃ©ens, vous pouvez les trouver dans [Bool]
//    (utiliser [Require Import Bool.]).
//*)
//
//Lemma evenb_correct : forall n, evenb n = true -> even n.
//Proof.
//Admitted.
//
//Lemma evenb_complete : forall n, even n -> evenb n = true.
//Proof.
//Admitted.
//
//Definition evenb_spec : forall n, evenb n = true <-> even n.
//Proof.
//Admitted.
//
//(** Prouver [even_dec_bis : forall n, even n \/ ~ even n]
//    en utilisant [evenb_spec]. *)
//
//Lemma even_dec_bis : forall n, even n \/ ~ even n.
//Proof.
//Admitted.
//
//
//(** Exercice 6 *)
//(** retour des listes *)
//Variable A : Type.
//
//Inductive mem : A -> list A -> Prop :=
//  mem_head : forall x l, mem x (cons x l)
//| mem_tail : forall x y l, 
//   mem x l -> mem x (cons y l).
//
//                                            
// Check app.
//
//Print app.
//
//Lemma app_left : forall l1 l2 x,
//mem x l1 -> mem x (app l1 l2).
//Proof.
//Admitted.
//
//Lemma app_or : forall l1 l2 x, mem x (app l1 l2) -> mem x l1 \/ mem x l2.
//Proof.
//Admitted.
