constant symbol Set : TYPE;
injective symbol τ : Set → TYPE; builtin "T" ≔ τ;

symbol mys : TYPE;
symbol myop :  mys →  mys →   mys;

symbol testfun : Π (Func : Set) (Hom : τ Func → Set) (Comp : Π [F : τ Func]  , τ (Hom F)) ,
 mys;

rule (myop (@testfun $Func $Hom $Comp ) (@testfun $Func $Hom $Comp    ) )
    ↪  (@testfun $Func $Hom $Comp ) ;
