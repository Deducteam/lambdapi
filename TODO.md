TODO
====

Index and search
----------------

* After "Number of results: 3" there is a missing CRLF

* why type only supports? =
  also doc is wrong, but I suppose code is wrong

* concl = _
  justifications include the following that are not expected
  $0.[V#] occurs inside the spine of the type and
  $0.[V#] occurs inside the hypothesis of the type and
  $0.[V#] occurs as the exact hypothesis of the type and
  $0.[V#] occurs as the exact conclusion of the type and
  $0.[V#] occurs inside the conclusion of the type and

* CLI interface: it tries to render way too many results
  and it takes ages

* Too many results found?

anywhere >= (Π x: _, (= _ V# V#))
anywhere >= (Π x: _, (= _ x x))

* html tags in textual output :-(

* would it be more reasonable to save the normalization rules
  when the index is created and apply them as default when searching,
  in particular when searching as a lambdapi command?

* normalize queries when given as commands in lambdapi

* alignments with same name ==> automatic preference?

* better pagination
