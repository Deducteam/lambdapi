Lambdapi user manual
====================

Who is this for?
----------------

The Lamdbapi user manual concerns mainly people who want to develop proofs or
encodings of logics using Lambdapi. People who want to use Lambdapi as an API
for proof interoperability should consult the OCaml documentation generated with
`make odoc` at the root of the git repository.

Where do I start?
-----------------

The documentation is available at <https://lambdapi.readthedocs.io>.

The online documentation generation is triggered each time new code is pushed to the master branch of the lambdapi repository on Github.
To this end, make sure the `.readthedocs.yaml` file is placed in the top-most directory of the Lambdapi repository and contains the well-suited configuration instructions as described in the [readthedocs documentation](https://docs.readthedocs.io/en/stable/config-file/index.html).

The Lamdbapi user manual can also be generated from the sources and browsed locally using any web
browser.

To generate the documentation, [Sphinx](https://www.sphinx-doc.org/)
and `sphinx_rtd_theme` are required.  They can be installed using
`pip` as follows:

```bash
sudo apt install python3-pip
pip install -U sphinx sphinx_rtd_theme
```

Change to directory `doc/` from the root of the sources
and use `make html` to generate `html` files into `doc/_build/html`.
The entry point of the documentation is `doc/_build/html/index.html`.

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

**Note:** BNF grammars are auto generated using 
  [Obelisk](https://github.com/Lelio-Brun/Obelisk). They should not be edited 
  directly.
