TODO
====

Typeclasses
----------------

* Allow typeclasses to have multiple arguments
* Multiple features could be implemented that are present in Davide Fissore's
  [Rocq-elpi typeclass solver](https://github.com/LPCIC/coq-elpi/blob/master/apps/tc/README.md)
  (instance priority, input/output argument mode,
  non-backtracking instances, etc...)
* The typeclass solver uses Elpi's unification, which means it does not work
  modulo rewriting (for example, an instance of type `myclass (_ → _)` won't
  work on a goal of type `myclass (El (arr _ _))` even with
  `rule El (arr $x $y) ↪ $x → $y;`)
  - Not necessarily an issue, we will see if cases arise
* It would be useful to have some form of record syntax, goes well with typeclasses.
  - See tests/OK/elpi_isa_test.lp, would look much better with record syntax.

Elpi
----------------

* With the Elpi integration, almost everything needed to add Elpi as a tactic
  language is here.
* One main issue could be tactic argument parsing: distinguish integers,
  lambdapi terms, strings.
* Elpi advantages for tactics:
  - HOAS and term quotation make it very easy to work with Lambdapi terms.
  - It is a full programming language, with easy possibility to define
    data structures, a standard library, and access to builtin functions
    from Ocaml for integers, strings, sets...
  - Lambda prolog means full support for backtracking and automated search.
  - Since Lambdapi's code is quite short, and thanks to Elpi's foreign
    function interface, it is quite easy to give access to interaction
    with most features of Lambdapi. Already included: typing computation,
    reduction (modulo rewriting), raising warnings and errors.
  - Since version 4.1., Elpi has a plugin and package system, where one can
    load Elpi files (and thus tactics) from another opam package.
  - It could be possible to copy code from Rocq tactics written in Elpi and
    adapt them.
    + This includes for example the lra, nra, psatz and ring tactics
      written partially in Elpi in the mathcomp library.

Index and search
----------------

* @abdelghani include in HOL2DK_indexing git sub-repos of
  coq-hol-light-real-with-N and coq-hol-light
  and automatize the generation of the file to output Rocq sources

* @abdelghani
  - (maybe?) allow an --add-examples=FNAME to include in the
    generated webpage an HTML snippet (e.g. with examples or
    additional infos for that instance)

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

* what notations for Rocq should websearch know about;
  right now they are in:
   - notation.lp file
     problem: if you want to add a lot of them, you need to
     require the definitions first (without requiring all the
     library...)
   - hard-coded lexing tokens in rocqLexer, e.g. /\ mapped to
     the corresponding Unicode character

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

* Misleading output for:

  anywhere >= (Π x: _, (= _ V# V#))
  anywhere >= (Π x: _, (= _ x x))

  Are there too many results?  NO, it's ok, but the output is misleading.
  The second form is equivalent
  to the first that is equivalent to  (_ -> (= _ V# V#)) that is what it is
  found. However it shows the pattern saying that " (Π x: _, (= _ x x))" was
  found, that is the misleading thing.
