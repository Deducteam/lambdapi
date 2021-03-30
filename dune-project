(lang dune 2.1)
(name lambdapi)

(using menhir 1.0)

(generate_opam_files true)

(source (github Deducteam/lambdapi))
(license CECILL-2.1)
(authors "Deducteam")
(maintainers "dedukti-dev@inria.fr")
(package
 (name lambdapi)
 (synopsis "Proof assistant based on the λΠ-calculus modulo rewriting")
 (description "Proof assistant based on the λΠ-calculus modulo rewriting,
mostly compatible with Dedukti.

This package contains both the `lambdapi` proof assistant and the `lp-lsp`
Language Server Protocol helper for IDEs to check lambdapi files.")
 (depends
  (ocaml (>= 4.07.0))
  (menhir (>= 20200624))
  (sedlex (>= 2.2))
  (alcotest :with-test)
  (bindlib (>= 5.0.1))
  (timed (>= 1.0))
  (pratter (>= 1.1))
  (why3 (>= 1.4.0))
  (yojson (>= 1.6.0))
  (cmdliner (>= 1.0.3))
  (stdlib-shims (>= 0.1.0))))
