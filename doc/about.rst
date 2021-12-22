What is Lambdapi?
=================

Lambdapi is an interactive proof system featuring dependent types like
in Martin-Lőf's type theory, but allowing to define objects and types
using oriented equations, aka rewriting rules, and reason modulo those
equations.

This allows to simplify some proofs, and formalize complex
mathematical objects that are otherwise impossible or difficult to
formalize in more traditional proof systems.

Lambdapi can also take as input `Dedukti`_ files, and can thus be used
as an interoperability tool.

Lambdapi is a logical framework and does not come with a pre-defined
logic. However, it is easy to define a logic by a few symbols and
rules. See for instance, the file `FOL.lp
<https://github.com/fblanqui/lib/blob/master/FOL.lp>`__ which defines
(polymorphic) first-order logic. There also exist definitions for the
logics of HOL, Coq or Agda.

Here are some of the features of Lambdapi:

- Emacs and VSCode plugins (based on LSP)
- support for unicode (UTF-8) and user-defined infix operators
- symbols can be declared commutative, or associative and commutative
- some arguments can be declared as implicit: the system will try to find out their value automatically
- symbol and rule declarations are separated so that one can easily define inductive-recursive types or turn a proved equation into a rewriting rule
- support for interactive resolution of typing goals, and unification goals as well, using tactics
- a rewrite tactic similar to the one of SSReflect in Coq
- the possibility of calling external automated provers
- a command is provided for automatically generating an induction principle for (mutually defined) strictly-positive inductive types
- Lambdapi can call external provers for checking the confluence and termination of user-defined rewriting rules by translating them to the `XTC <https://github.com/TermCOMP/TPDB/blob/master/xml/xtc.xsd>`__ and `HRS <http://project-coco.uibk.ac.at/problems/hrs.php>`__ formats used in the termination and confluence competitions

Some bibliographic references
-----------------------------

-  `Dedukti: a Logical Framework based on the λΠ-Calculus Modulo
   Theory <http://www.lsv.fr/~dowek/Publi/expressing.pdf>`__, Ali Assaf,
   Guillaume Burel, Raphaël Cauderlier , David Delahaye, Gilles Dowek,
   Catherine Dubois, Frédéric Gilbert, Pierre Halmagrand, Olivier
   Hermant, and Ronan Saillard. Draft, 2016.

-  `Typechecking in the λΠ-Calculus Modulo: Theory and
   Practice <https://hal.inria.fr/tel-01299180>`__, Ronan Saillard. PhD
   thesis, 2015.

-  `Definitions by rewriting in the Calculus of
   Constructions <https://doi.org/10.1017/S0960129504004426>`__,
   Frédéric Blanqui, in Mathematical Structures in Computer Science
   15(1):37-92.

-  `The New Rewriting Engine of
   Dedukti <https://www.semanticscholar.org/paper/The-New-Rewriting-Engine-of-Dedukti-Hondet-Blanqui/8ff6f9790779f9345ffa9bb02679b40e8d1d83aa>`__,
   Gabriel Hondet and Frédéric Blanqui, 2020.

-  `Hints in
   Unification <http://www.cs.unibo.it/~asperti/PAPERS/tphol09.pdf>`__,
   Andrea Asperti, Wilmer Ricciotti, Claudio Sacerdoti Cohen and Enrico
   Tassi.

-  More papers can be found
   `here <https://haltools.inria.fr/Public/afficheRequetePubli.php?labos_exp=deducteam&CB_auteur=oui&CB_titre=oui&CB_identifiant=oui&CB_article=oui&langue=Anglais&tri_exp=annee_publi&tri_exp2=typdoc&tri_exp3=date_publi&ordre_aff=TA&Fen=Aff&css=../css/VisuRubriqueEncadre.css>`__.

.. _Dedukti: https://deducteam.github.io/
.. _Coq: http://coq.inria.fr
.. _Matita: http://matita.cs.unibo.it/
.. _OpenTheory: http://www.gilith.com/opentheory/
