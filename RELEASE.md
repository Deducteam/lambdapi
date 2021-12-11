TODO list for a new release on github and opam using [dune-release](https://github.com/ocamllabs/dune-release)
-------------------------------------------------------------------

- create a new branch for preparing the release

- in CHANGES.md, replace Unreleased by the new release number + date + summary of the most important changes

- update AUTHORS.md if needed

- update dune-project + do make (to regenerate lambdapi.opam)

- opam install dune-release

- dune-release distrib + fix problems

- commit, push, create a PR, merge

In a new directory:

- git clone git@github.com:fblanqui/lambdapi.git

- git checkout release

- dune-release tag

- dune-release distrib

- create new token public_repo on https://github.com/settings/tokens/new

- dune-release publish distrib

- dune-release opam pkg

- dune-release opam submit
