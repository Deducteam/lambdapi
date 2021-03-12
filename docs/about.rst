What is Lambdapi?
=================

The Lambdapi system is several things! It is intended to replace `Dedukti`_ in
a near future. It extends Dedukti with new features, especially interactive
proof development.

A logical framework
-------------------

The core theoretical system of Lambdapi is a logical framework based on the
λΠ-calculus modulo rewriting. It is hence a dependent type theory that is very
similar to Martin-Lőf’s dependent type theory (i.e., it is an extension of the
simply-typed λ-calculus), but it has the peculiarity of allowing the user to
define function symbols with associated rewriting rules. Although the system
seems to be very simple at first, it is surprisingly powerful. In particular,
it allows the encoding of the theories behind Coq or HOL.

A tool for interoperability of proof systems
--------------------------------------------

The ability to encode several rather different systems make of Lambdapi an
ideal target for proof interoperability. Indeed, one can for example export a
proof written in `Matita`_ (an implementation of the calculus of inductive
constructions) to the `OpenTheory`_ format (shared between several
implementations of HOL).

An interactive proof system
---------------------------

Being aimed at interoperability, Dedukti was never intended to become a tool
for writing proofs directly. On the contrary, Lambdapi is aimed at providing
an interactive proof mechanism, while remaining compatible with ``Dedukti``
(and its interoperability capabilities).

Here is a list of new features brought by Lambdapi: - a new syntax suitable
for proof developments (including tactics), - support for unicode (UTF-8) and
(user-defined) infix operators, - automatic resolution of dependencies, - a
simpler, more reliable and fully documented implementation, - more reliable
operations on binders thanks to the Bindlib library, - a general notion of
metavariables, useful for implicit arguments and goals.

An experimental proof system
----------------------------

Finally, let us note that Lambdapi is to be considered (at least for now) as
an experimental proof system based on the λΠ-calculus modulo rewriting. It is
aimed at exploring (and experimenting with) the many possibilities offered by
rewriting, and the associated notion of conversion. In particular, it leads to
simple proofs, where many details are delegated to the conversion rule.

Although the language may resemble `Coq`_ at a surface level, it is
fundamentally different in the way mathematics can be encoded. It is yet
unclear whether the power of rewriting will be a significant advantage of
Lambdapi over systems like Coq. That is something that we would like to
clarify (in the near future) thanks to Lambdapi.

Bibliographic references
------------------------

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
