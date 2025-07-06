TODO
====

Index and search
----------------

* After "Number of results: 3" there is a missing CRLF

* why type only supports? =
  also doc is wrong, but I suppose code is wrong

* CLI interface: it tries to render way too many results
  and it takes ages

* html tags in textual output :-(

* would it be more reasonable to save the normalization rules
  when the index is created and apply them as default when searching,
  in particular when searching as a lambdapi command?

* normalize queries when given as commands in lambdapi

* alignments with same name ==> automatic preference?

* better pagination

Performance improvements
------------------------

* see if compressing the index yields a significant gain

* currently in a query like 'concl = _' it builds an extremely large matching set
  and THEN it filters out the justifications that have Concl Exact; maybe we
  could save a lot of time anticipating the filtrage

Misleading output
-----------------

+ Too many results found?

anywhere >= (Π x: _, (= _ V# V#))
anywhere >= (Π x: _, (= _ x x))

NO, it's ok, but the output is misleading. The second form is equivalent
to the first that is equivalent to  (_ -> (= _ V# V#)) that is what it is
found. However it shows the pattern saying that " (Π x: _, (= _ x x))" was
found, that is the misleading thing.

