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
 (synopsis "Proof assistant for the λΠ-calculus modulo rewriting")
 (description
"This package provides:
- A lambdapi command for checking .lp or .dk files,
translating .dk files to .lp files, or launching
an LSP server for editing .lp files.
- A rich Emacs mode based on LSP (available also on MELPA).
- A very basic mode for Vim.
- OCaml libraries.
A VSCode extension is available on the VSCode Marketplace.

Lambdapi user manual: https://lambdapi.readthedocs.io/

Lambdapi provides a rich type system with dependent types.
In Lambdapi, one can define both type and function symbols
by using rewriting rules (oriented equations). The declaration
of symbols and rewriting rules is separated so that one can
easily define inductive-recursive types.

Lambdapi provides interactive modes for proving both unification
goals and typing goals, and tactics for solving them step by step.
In particular, Lambdapi provides a rewrite tactic similar to
the one of SSReflect, and a why3 tactic for calling external
automated provers through the Why3 platform.

Lambdapi provides a basic module and package system.

Finally, rewrite rules can be exported to the TRS and XTC
formats for checking confluence and termination
with external tools.")
 (depends
  (ocaml (>= 4.08.0))
  (menhir (>= 20200624))
  (sedlex (>= 2.2))
  (alcotest :with-test)
  (bindlib (>= 5.0.1))
  (timed (>= 1.0))
  (pratter (>= 1.2))
  (why3 (>= 1.4.0))
  (yojson (>= 1.6.0))
  (cmdliner (>= 1.0.3))
  (stdlib-shims (>= 0.1.0))))
