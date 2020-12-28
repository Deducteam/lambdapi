Overview of directories and files
=================================

- ``examples/``: some examples (integration tests).

- ``import/``: a test suite on imports.
More precisely, here we check the commands:
  - require
  - require as
  - open
and we check the possible paths too.

- ``inductive/``: a test suite on inductive types.
More precisely, here we check the commands:
  - inductive

- ``parsing/``: a test suite on parsing.
More precisely, here we check:
  - empty file
  - escaped identifier

- ``queries/``: a test suite on queries.
More precisely, here we check the commands:
  - assert
  - assertnot
  - type
  - compute

- ``rewriting/``: a test suite on rules.
More precisely, here we check:
  - arity
  - free variable in LHS
  - patterns
  - non linearity
  - order
  - instanciation
  - performance

- ``scoping/``: a test suite on terms.
More precisely, here we check:
  - implicit argument
  - lambda construction (with substitution)
  - let construction
  - wildcard

- ``set_option/``: a test suite on set option.
More precisely, here we check the commands:
  - set unif_rule
  - set verbose   (no tests)
  - set debug     (no tests)
  - set builtin
  - set prefix
  - set infix
  - set prover    (no tests)
  - set prover_timeout (no tests)
  - set declared
  - set flag eta_equality
             print_domains   (no tests)
             print_implicits (no tests)
             print_meta_type (no tests)
             print_contexts  (no tests)
             print_domains   (no tests)
  - set quantifier
  
- ``symbol/``: a test suite on symbols.
More precisely, here we check:
  - declaration
  - opacity

- ``tactics/``: a test suite on tactics.
More precisely, here we check the commands:
  - print     (no tests)
  - end / admit / abort (no tests)
  - focus     (no tests)
  - fail      (no tests)
  - proofterm (no tests)
  - solve
  - assume
  - simpl
  - refine
  - apply
  - why3
  - reflexivity
  - symmetry
  - rewrite
 
