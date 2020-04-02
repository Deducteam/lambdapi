// Cours et exercices de la découverte de lambdapi
// Inspiré de la version Coq de Catherine Dubois

require open tests.preuves_Ledein.constructor

// Leibniz equality
constant symbol eq {a} : τ a ⇒ τ a ⇒ Prop
set infix 1 "=" ≔ eq
constant symbol eq_refl {a} (x:τ a) : P (x = x)
constant symbol eq_ind {a} (x y:τ a) :
       P (x = y) ⇒ ∀p, P (p y) ⇒ P (p x)

////////////////////////////////////
// Avant de prendre la route...
////////////////////////////////////

// Inductive route : Type :=
// | departementale : route
// | nationale : route
// | autoroute : route.                                  

constant symbol route          : Set // FB mieux ?
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
                               
theorem agrandir_test :
π ((agrandir (agrandir nationale)) = autoroute)
proof
 simpl
 refine eq_refl autoroute
qed

//Inductive terrain : Type :=
//| t_terre : terrain
//| t_route : route -> terrain
//| t_batiment : terrain.

constant symbol terrain    : Set // FB mieux ?
definition Ter ≔ τ terrain
constant symbol t_terre    : Ter
constant symbol t_route    : R ⇒ Ter
constant symbol t_batiment : Ter

//Check (t_route nationale).
type (t_route nationale)

/////////////////////////////
// Exercice 1. - Booléen
/////////////////////////////

require open tests.preuves_Ledein.myLib.Bool
constant symbol true : B
constant symbol false : B
                        
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

// Définir les fonctions [andb] et [orb] sur les booléens

// Definition andb b1 b2 :=
//  match b1 with
//  | true => b2
//  | false => false
//  end.

symbol andb : B ⇒ B
rule andb false _  → false
 and andb _ false  → false
 and andb &b1 true → &b1
 and andb true &b2 → &b2

// Definition orb b1 b2 :=
//   match b1 with
//   | true => true
//   | false => b2
//   end.

symbol orb : B ⇒ B
rule orb true _  → true
 and orb _ true  → true
 and orb &b1 false → &b1
 and orb false &b2 → &b2
