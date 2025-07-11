TODO
====

Index and search
----------------

* @abdelghani include in HOL2DK_indexing git sub-repos of
  coq-hol-light-real-with-N and coq-hol-light
  and automatize the generation of the file to output Coq sources

* when disambiguating an identifier, after rewriting one could be
  left with just one id (not working now)

* add notations for Coq stdlib to websearch (using Pratter?)

* syntactic sugar for regular expressions / way to write a regular
  expression - only query efficiently
    (concl = _ | "regexpr")

* normalize queries when given as commands in lambdapi

* generate mappings from LP to V automatically with HOL2DK and find
  what to do with manually written files; also right now there are
  mappings that are lost and mappings that are confused in a many-to-one
  relation

Think about
-----------

* alignments with same name ==> automatic preference?

* would it be more reasonable to save the normalization rules
  when the index is created and apply them as default when searching,
  in particular when searching as a lambdapi command?

* package management

* update index / deindex (it should work at package level)

* more external sources when showing query results, including Git repos

* VS code integration: right now lambdapi works on the current development
  mixed with remote, but different sets of rewriting rules would make sense;
  should it instead only work with the current development and dispatch
  queries via VS code to a remote websearch?

* ranking

Performance improvements
------------------------

* see if compressing the index yields a significant gain

* currently in a query like 'concl = _' it builds an extremely large matching set
  and THEN it filters out the justifications that have Concl Exact; maybe we
  could save a lot of time anticipating the filtrage

Documentation
-------------

* fix the doc: not only "anywhere" but also "type" can be paired
  only with ">="; maybe make it explicit that to match exactly the
  type of a constant one should use "spine ="

* document new features, e.g. -sources (and find better
  terminology), deindex

* document Coq syntax in websearch

* document require ... as Foo: using Foo.X in the query already
  works (pure magic!); of course it does not work when using
  regular expressions [ check before! ]

* Misleading output for:

  anywhere >= (Π x: _, (= _ V# V#))
  anywhere >= (Π x: _, (= _ x x))

  Are there too many results?  NO, it's ok, but the output is misleading.
  The second form is equivalent
  to the first that is equivalent to  (_ -> (= _ V# V#)) that is what it is
  found. However it shows the pattern saying that " (Π x: _, (= _ x x))" was
  found, that is the misleading thing.
