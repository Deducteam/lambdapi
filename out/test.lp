require coq.cupicef as bios;
require coq.Coq__Relations__Relation__Definitions;
require coq.Coq__Classes__RelationClasses as x;
require coq.Coq__Init__Logic as y;

open "tc" coq.Coq__Classes__RelationClasses;

flag "print_implicits" on; // default is off
flag "print_contexts" on; // default is off
flag "print_domains" on; // default is off
flag "print_meta_types" on; // default is 

type y.eq;
type x.reflexivity;

// ENRICO: bug in readback of terms in the query,the context is empty 
// We hack it with a section variable
symbol A : bios.Univ (bios.type (bios.s bios.z));

// cast from Type[1] to Type[2]
coerce_rule coerce (bios.Univ (bios.{|type|} (bios.s bios.z))) (bios.Univ (bios.{|type|} (bios.s (bios.s bios.z)))) $X ↪ (bios.cast (bios.axiom (bios.{|type|} (bios.s bios.z)))
 (bios.axiom (bios.{|type|} (bios.s (bios.s bios.z))))
 (bios.univ (bios.{|type|} (bios.s bios.z))
  (bios.axiom (bios.{|type|} (bios.s bios.z))) bios.I)
 (bios.univ (bios.{|type|} (bios.s (bios.s bios.z)))
  (bios.axiom (bios.{|type|} (bios.s (bios.s bios.z)))) bios.I)
 bios.I
 $X);

//debug +i;
//debug +e;

type x.reflexivity A (y.eq A) _ _;
type x.match____RewriteRelation _ A (y.eq A) _ _ _;

/*
type
x.reflexivity A (y.eq
(
    
bios.cast
(bios.axiom (bios.{|type|} (bios.s bios.z)))
(bios.axiom (bios.{|type|} (bios.s (bios.s bios.z))))
(bios.univ (bios.{|type|} (bios.s bios.z))
 (bios.axiom (bios.{|type|} (bios.s bios.z))) bios.I)
(bios.univ (bios.{|type|} (bios.s (bios.s bios.z)))
 (bios.axiom (bios.{|type|} (bios.s (bios.s bios.z))))
 bios.I)
_

A)) _ _;
*/
