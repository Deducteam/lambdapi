Utype : Type.
Ukind : Type.

etype : Utype ⇒ Type.
ekind : Ukind ⇒ Type.

dottype : Ukind.

dotpi1 : x:Utype ⇒ y:(etype x ⇒ Utype) ⇒ Utype.
dotpi2 : x:Utype ⇒ y:(etype x ⇒ Ukind) ⇒ Ukind.
dotpi3 : x:Ukind ⇒ y:(ekind x ⇒ Utype) ⇒ Utype.
dotpi4 : x:Ukind ⇒ y:(ekind x ⇒ Ukind) ⇒ Ukind.

[x y] etype (dotpi1 x y) → w:etype x ⇒ etype (y w).
[x y] etype (dotpi3 x y) → w:ekind x ⇒ etype (y w).

[] ekind dottype → Utype.
[x y] ekind (dotpi2 x y) → w:etype x ⇒ ekind (y w).
[x y] ekind (dotpi4 x y) → w:ekind x ⇒ ekind (y w).

a : x:Utype ⇒ y:etype x ⇒ etype x.
[] a → λx:Utype. λy:etype x. y.

// Logic

False : Utype.
True  : Utype.
I : etype True.

eq  : t:Utype ⇒ etype t ⇒ etype t ⇒ Type.
eq_ : t:Utype ⇒ etype t ⇒ etype t ⇒ Utype.

[t x y] eq t x y → etype (eq_ t x y).

refl_equal : t:Utype ⇒ x:etype t ⇒ eq t x x.

eq_rec : t:Utype
  ⇒ x:etype t
  ⇒ p:(etype t ⇒ Utype)
  ⇒ g:etype (p x)
  ⇒ y:etype t
  ⇒ h:eq t x y
  ⇒ etype (p y).

f_equal : A:Utype
  ⇒ B:Utype
  ⇒ f:(etype A ⇒ etype B)
  ⇒ x:etype A
  ⇒ y:etype A
  ⇒ H:eq A x y
  ⇒ eq B (f x) (f y).

[] f_equal →
  λA:Utype. λB:Utype.
  λf:(etype A ⇒ etype B). λx:etype A. λy:etype A. λH:eq A x y.
  eq_rec A x (λz:etype A. eq_ B (f x) (f z)) (refl_equal B (f x)) y H.

// Peano

nat_ : Utype.

nat : Type.

[] nat → etype nat_.

Z : nat.

S : nat ⇒ nat.

nat_rec : t:Utype
  ⇒ etype t
  ⇒ (nat ⇒ etype t ⇒ etype t)
  ⇒ nat
  ⇒ etype t.

[t a f]   nat_rec t a f Z     → a.
[t a f n] nat_rec t a f (S n) → f n (nat_rec t a f n).

plus : nat ⇒ nat ⇒ nat.
[] plus → λx:nat. λy:nat. nat_rec nat_ Z (λx:nat. λy:nat. y) x.

plus2 : nat ⇒ nat ⇒ nat.
[x]   plus2 x     Z     → x.
[x]   plus2 Z     x     → x.
[x y] plus2 x     (S y) → S (plus2 x y).
[x y] plus2 (S x) y     → S (plus2 x y).

eq_S : x:nat
  ⇒ y : nat
  ⇒ eq nat_ x y
  ⇒ eq nat_ (S x) (S y).

[] eq_S → f_equal nat_ nat_ S.

eq_S2 : etype (dotpi1 nat_ (λx:nat.
  dotpi1 nat_ (λy:nat.
  dotpi1 (eq_ nat_ x y) (λh:eq nat_ x y. eq_ nat_ (S x) (S y))))).

[] eq_S2 → eq_S.

pred : nat ⇒ nat.
[] pred → nat_rec nat_ Z (λx:nat. λy:nat. x).

pred2 : nat ⇒ nat.
[]  pred2 Z     → Z.
[x] pred2 (S x) → x.

pred_Sn : n : nat ⇒ eq nat_ n (pred (S n)).
[] pred_Sn → λn:nat. refl_equal nat_ n.
