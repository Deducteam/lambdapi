TODO list for a new release on github and opam using [dune-release](https://github.com/ocamllabs/dune-release)
-------------------------------------------------------------------

- git checkout -b release

- in CHANGES.md, replace Unreleased by the new release number + date + summary of the most important changes

- update AUTHORS.md if needed

- update dune-project + do make (to regenerate lambdapi.opam)

- opam install dune-release

- dune-release distrib + fix problems

- commit and push

In a new directory:

- git clone git@github.com:fblanqui/lambdapi.git

- git checkout release

- git tag -d $version + git fetch + git merge after changes

- dune-release tag

- dune-release distrib

- create new token public_repo on https://github.com/settings/tokens/new

- dune-release publish distrib

- dune-release opam pkg

- dune-release opam submit

Once published on opam:

- merge PR on master
