(lang dune 3.7)

(generate_opam_files false)

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
  (ocaml (>= 4.08.0))
  (menhir (>= 20200624))
  (sedlex (>= 3.2))
  (alcotest :with-test)
  (alt-ergo :with-test)
  (dedukti (and :with-test (>= 2.7)))
  (bindlib (>= 5.0.1))
  (timed (>= 1.0))
  (pratter (and (>= 3.0.0) (< 4)))
  (camlp-streams (>= 5.0))
  (why3 (and (>= 1.6.0) (< 1.8~)))
  (yojson (>= 1.6.0))
  (cmdliner (>= 1.1.0))
  (stdlib-shims (>= 0.1.0))
  (lwt_ppx (>= 1.0.0))
  (dream (>= 1.0.0~alpha3))))
