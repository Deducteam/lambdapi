(lang dune 3.7)
(using dune_site 0.1)
(generate_opam_files true)

(name lambdapi)
(source (github Deducteam/lambdapi))
(authors "Deducteam")
(maintainers "dedukti-dev@inria.fr")
(license CECILL-2.1)

(using menhir 2.0)

(package
 (name lambdapi)
 (synopsis "Proof assistant for the λΠ-calculus modulo rewriting")
 (description

"Lambdapi is an interactive proof assistant for the λΠ-calculus modulo
rewriting. It can call external automated theorem provers via Why3.
The user manual is on https://lambdapi.readthedocs.io/.
A standard library and other developments are available on
https://github.com/Deducteam/opam-lambdapi-repository/. An extension
for Emacs is available on MELPA. An extension for VSCode is available
on the VSCode Marketplace. Lambdapi can read Dedukti files. It
includes checkers for local confluence and subject reduction. It also
provides commands to export Lambdapi files to other formats or
systems: Dedukti, Coq, HRS, CPF.")

 (depends
  (ocaml (>= 4.10))
  (dream-pure (>= 1.0.0~alpha2))
  (dream-httpaf (>= 1.0.0~alpha3))
  (dream (>= 1.0.0~alpha6))
  (menhir (>= 20200624))
  (sedlex (>= 3.2))
  (alcotest :with-test)
  (alt-ergo :with-test)
  (dedukti (and :with-test (>= 2.7)))
  (timed (>= 1))
  (pratter (and (>= 5) (< 6)))
  (camlp-streams (>= 5))
  (why3 (>= 1.8))
  (yojson (>= 1.6))
  (cmdliner (>= 1.1))
  (stdlib-shims (>= 0.1))
  (odoc :with-doc)
  (lwt_ppx (>= 1))
  (uri (>= 1.1))
 )
 (sites (share server_resources))
)
