#### Prepare for modern versions of OCaml (2020-03-26)

 - Use `Stdlib` instead of `Pervasives` (enforced by sanity checks).
 - Rely on `stdlib-shims` to provide `Stdlib` on older version of OCaml.

#### Let bindings (2020-03-26)

Adding let-bindings to the terms structure.
- Contexts can now contain term definitions.
- Unification is carried out with a context.
- Equality modulo can use a context to unfold the definition of variables.

#### File management and module mapping (2020-03-20)

 - New module system.
 - Revised command line arguments parsing and introduce subcommands.
 - LSP server is now a Lambdapi subcommand: run with `lambdapi lsp`.
 - New `--no-warning` option (fixes #296).

#### Trees simplification (2019-12-05)

Simplification of the decision tree structure
 - trees do not depend on term variables;
 - tree constructor type depends on generated at compile-time
   branch-wise unique integral identifiers;
 - graph output is more consistent: variables are the same in the
   nodes and the leaves.

### 1.0 (2018-11-28)

First major release of Lambdapi. It introduces:
 - a new syntax for developing proofs in the system,
 - basic support for infix operators,
 - call to external confluence checker with the same API as Dedukti,
 - more things.
 - Consolidate the LSP OPAM package into the main one (@ejgallego)

### 0.1 (2018-09-19)

First release of Lambdapi.
