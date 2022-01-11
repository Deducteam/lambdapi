/* Encoding of functional Pure Type Systems after "Embedding Pure Type Systems
in the Lambda-Pi-Calculus Modulo", by Denis Cousineau and Gilles Dowek,
TLCA 2007, 10.1007/978-3-540-73228-0_9.

A functional PTS is described by a set S of sorts, a functional
relation A ⊆ S², and a functional relation R ⊆ A²xA. To represent
sets, we use a type Set of set codes and a function F interpreting set
codes into types. */

constant symbol Set : TYPE;
symbol F : Set → TYPE;

constant
symbol U (s : Set) (a : F s → F s → Set) (r : F s → F s → F s → Set)
  : F s → TYPE;

symbol El (s : Set) (a : F s → F s → Set) (r : F s → F s → F s → Set)
  [x : F s] : U s a r x → TYPE;

constant symbol u s a r x₁ [x₂] : F (a x₁ x₂) → U s a r x₂;

rule El $s $a $r (u _ _ _ $x₁ _) ↪ U $s $a $r $x₁;

constant
symbol prod (s : Set) (a : F s → F s → Set) (r : F s → F s → F s → Set)
  [x₁ x₂ x₃] : F (r x₁ x₂ x₃) →
  Π t : U s a r x₁, (El s a r t → U s a r x₂) → U s a r x₃;

rule El $s $a $r (prod _ _ _ _ $t $u)
  ↪ Π x : El $s $a $r $t, El $s $a $r ($u x);
