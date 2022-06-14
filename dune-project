(lang dune 2.7)

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
"This package provides:
- A lambdapi command for checking .lp or .dk files,
translating .dk files to .lp files and vice versa,
or launching an LSP server for editing .lp files.
- A library of logic definitions and basic definitions and proofs
on natural numbers and polymorphic lists.
- A rich Emacs mode based on LSP (available on MELPA too).
- A basic mode for Vim.
- OCaml libraries.
A VSCode extension is available on the VSCode Marketplace.

Find Lambdapi user manual on https://lambdapi.readthedocs.io/.

Lambdapi provides a rich type system with dependent types.
In Lambdapi, one can define both type and function symbols
by using rewriting rules (oriented equations). The declaration
of symbols and rewriting rules is separated so that one can
easily define inductive-recursive types for instance.
Rewrite rules can be exported to the TRS and XTC formats
for checking confluence and termination with external tools.
A symbol can be declared associative and commutative.
Lambdapi supports unicode symbols and infix operators.

Lambdapi does not come with a pre-defined logic. It is a
powerful logical framework in which one can easily define
its own logic and build and check proofs in this logic.
There exist .lp files defining first or higher-order logic
and complex type systems like in Coq or Agda.

Lambdapi provides a basic module and package system,
interactive modes for proving both unification goals
and typing goals, and tactics for solving them step by step.
In particular, a rewrite tactic like in SSReflect, and
a why3 tactic for calling external automated provers through
the Why3 platform.")
 (depends
  (ocaml (>= 4.08.0))
  (menhir (>= 20200624))
  (sedlex (>= 2.2))
  (alcotest :with-test)
  (alt-ergo (and :with-test (<= 2.4.0) (>= 2.0)))
  (bindlib (>= 5.0.1))
  (timed (>= 1.0))
  (pratter (= 1.2))
  (why3 (= 1.4.0))
  (yojson (>= 1.6.0))
  (cmdliner (and (>= 1.0.3) (<= 1.0.4)))
  (stdlib-shims (>= 0.1.0))))
