Lambdapi user manual
====================

Who is this for?
----------------

The Lamdbapi user manual concerns mainly people that want to develop proofs or
encodings of logics using Lambdapi. People who want to use Lambdapi as an API
for proof interoperability should consult the OCaml documentation generated with
`make doc` at the root of the git repository.

Where do I start?
-----------------

The documentation is available at <https://lambdapi.readthedocs.io>.

It can also, be generated from the sources and browsed locally using any web
browser.

To generate the documentation, 
[Sphinx](https://www.sphinx-doc.org/en/master/index.html) is required
(it can be installed, using `pip`, with `pip install -U sphinx`).
Change to directory `docs/` from the  root of the sources repository,
and use `make html` to generate `html` files into `docs/_build/html`,
that can be browsed with `xdg-open docs/_build/html/index.html`.

How do I contribute?
--------------------

We will gladly accept any contribution to the documentation. If something is
unclear, please tell us using the 
[issue tracker](https://github.com/Deducteam/lambdapi/issues), using the 
"documentation" tag.

To write documentation, open a pull request. We have a few guidelines on writing
[restructured text](https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html):

* even though any kind of underlining can be used to establish title hierarchy 
  (hierarchy is established by order of appearance), we favour, in decreasing
  order of importance (from top title to paragraph),
  1. `====`
  2. `----`
  3. `^^^^`
  4. `''''`
* for lists, use stars `*`.
* BNF grammars are auto generated using 
  [Obelisk](https://github.com/Lelio-Brun/Obelisk), they should not be edited 
  directly.
