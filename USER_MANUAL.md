Lambdapi user manual
====================

This document explains several of the concepts behind `lambdapi` and serves as
a user documentation. Installation instructions can be found in the repository
(see [README.md](README.md)). Here is a rough summary:
```bash
git clone https://github.com/Deducteam/lambdapi.git
cd lambdapi
make && make install
```

What is Lambdapi?
-----------------

The `lambdapi` system is several things!

### A logical framework

The core theoretical system of `lambdapi` is a logical framework based on  the
λΠ-calculus modulo rewriting. It is hence a dependent type theory that is very
similar to Martin-Lőf's dependent type theory (i.e., it is an extension of the
simply-typed λ-calculus),  but it has the peculiarity of allowing the user  to
define function symbols with associated rewriting rules.  Although the  system
seems to be very simple at first, it is surprisingly powerful.  In particular,
it allows the encoding of the theories behind Coq or HOL.

### A tool for interoperability of proof systems

The ability to encode several rather different systems make of `lambdapi` (and
its predecessor `Dedukti`) an ideal target for proof interoperability. Indeed,
one can for example export a proof written in Matita (an implementation of the
calculus of inductive constructions) to the OpenTheory format (shared  between 
several implementations of HOL).

### An interactive proof system

Being aimed at interoperability, `Dedukti` was never intended to become a tool
for writing proofs directly. On the contrary, `lambdapi` is aimed at providing
an interactive proof mechanism, while remaining compatible with `Dedukti` (and
its interoperability capabilities).

Here is a list of new features brought by `lambdapi`:
 - a new syntax suitable for proof developments (including tactics),
 - support for unicode (UTF-8) and (user-defined) infix operators,
 - automatic resolution of dependencies,
 - a simpler, more reliable and fully documented implementation,
 - more reliable operations on binders thanks to the Bindlib library,
 - a general notion of metavariables, useful for implicit arguments and goals.

### An experimental proof system

Finally, let us note that `lambdapi` is to be considered (at least for now) as
an experimental proof system based on the λΠ-calculus modulo rewriting.  It is
aimed at exploring (and experimenting with)  the many possibilities offered by
rewriting, and the associated notion of conversion. In particular, it leads to
simple proofs, where many details are delegated to the conversion rule.

Although the language may resemble Coq at a surface level, it is fundamentally
different in the way mathematics can be encoded. It is yet unclear whether the
power of rewriting will be a significant advantage of `lambdapi` over  systems
like Coq. That is something that we would like to clarify (in the near future)
thanks to `lambdapi`.

Command line flags and tools
----------------------------

The installation of `lambdapi` give you:
 - a main executable named `lambdapi` in your `PATH`,
 - an OCaml library called `lambdapi`,
 - an LSP-compatible server called `lp-lsp` in your `PATH`,
 - a `lambdapi` mode for `Vim` (optional),
 - a `lambdapi` mode for `emacs` (optional).

### Main Lambdapi program

The `lambdapi` executable is the main program. It can be used to process files
written in the `lambdapi` syntax (with the ".lp" extension), and files written
in the legacy (Dedukti) syntax (with the ".dk" extension).

Several files can be given as command-line arguments, and they are all handled
independently (in the order they are given). Note that the program immediately
stops on the first failure, without going to the next file (if any).

**Important note:** the paths given on the command-line for input files should
be relative to the current directory. Moreover, they should neither start with
the `./` current directory marker, nor contain partent directory markers `..`.
This is due to the fact that the directory structure is significant due to the
treatment of modules (more details on that will be given later).

Command line flags can be used to control the behaviour of `lambdapi`. You can
use `lambdapi --help` to get a short description of the available flags.  The
available options are described in details below.

#### Mode selection

The `lambdapi` program may run in three different modes. The standard mode (it
is selected by default) parses, type-checks and handles the given files. Other
modes are selected with one of the following flags:
 - `--justparse` enables the parsing mode: the files are parsed and `lambdapi`
   only fails in case of parse error (variable scopes are not checked). In any
   case, the compilation of dependencies may be triggered in order to retrieve
   user-defined notations.
 - `--beautify` enables the pretty-printing mode: the files are printed to the
   standard output in `lambdapi` syntax.  This mode can be used for converting
   legacy syntax files (with the ".dk" extension) to the standard syntax. Note
   that, as for the parsing mode (`--justparse` flag),  the compilation of the
   dependencies of the input files may be triggered.

Note that when several mode selection flags are given,  only the latest one is
taken into account. Moreover, other command-line flags are ignored (except the
`--help` and `-help` flags).

#### Default mode flags

When in default mode, the following flags are available for configuration:
 - `--gen-obj` instructs `lambdapi` to generate object files for every checked
   module (including dependencies). Object files have the ".lpo" extension and
   they are automatically read back when necessary if they exist and are up to
   date (they are regenerated otherwise).
 - `--verbose <int>` sets the verbosity level to the given natural number (the
   default value is 1). A value of 0 should not print anything, and the higher
   values (up to 3) print more and more information.

#### Confluence checking

Confluence checking (and also termination) must be established for each of the
considered rewriting systems contained in `lambdapi` files. By default,  these
checks are not performed, and they must be explicitly requested.

We provide an interface to external confluence checkers using the TRS  format.
The `--confluence <cmd>` flag specifies the confluence-checking command to  be
used. The command is expected to behave as follows:
 - take the problem description (in `.trs` format) on its standard input,
 - output on its first line either `YES`, `NO` or `MAYBE`.

As an example,  `echo MAYBE` is the simplest possible (valid) confluence-check
that one may use.

For now, only the `CSI^ho` confluence checker has been tested with `lambdapi`.
It can be called in the following way.
```bash
lambdapi --confluence "path/to/csiho.sh --ext trs --stdin" input_file.lp
```

To generate the `.trs` file corresponding to some `lambdapi` file, one may use
a dummy confluence-checking command as follows.
```bash
lambdapi --confluence "cat > output.trs; echo MAYBE" input_file.lp
```

#### Termination checking

For now, there is no support for termination checking.

#### Debugging flags

The following flags may be useful for debugging:
 - `--debug <str>` enables the debugging modes specified by every character of
   the string `<str>`. Details on available character flags are obtained using
   the `--help` flag.
 - `--timeout <int>` gives up type-checking after the given number of seconds.
   Note that the timeout is reset between each file, and that the parameter of
   the command is expected to be a natural number.
 - `--toolong <flt>` gives a warning for each command (i.e., file item) taking
   more than the given number of seconds to be checked. The given parameter is
   expected to be a floating point number.

Finally, remember that `--help` or `-help` gives you a list of available flags
with a minimal documentation.

### Lambdapi OCaml library

The `lambdapi` OCaml library gives access to the core data structures that are
used by `lambdapi`. It can be used to experiment with the type-checker and the
rewriting engine of `lambdapi`, but also to propose new (compatible) tools. It
is currently used by the implementation of the LSP server (next section).

### Lambdapi LSP server

The `lambdapi` LSP server, called `lp-lsp`, implements an interface to editors
supporting the [LSP](https://github.com/Microsoft/language-server-protocol)
protocol. For now,  we support the `emacs` editor through the `eglot` package,
and also the `Atom` editor with a custom plugin.

See the file [lp-lsp/README.md](lp-lsp/README.md) for more details.

### Emacs mode

The `emacs` mode can be optionally installed using `make install_emacs` in the
`lambdapi` repository.  Support for the LSP server is enabled by default,  but
it requires the `eglot` plugin to be installed.

See the file [lp-lsp/README.md](lp-lsp/README.md) for more details.

### Vim mode

The `Vim` mode can be installed similarly using the command `make install_vim`
in the `lambdapi` repository. It does not yet have support for the LSP server.

### Atom mode

Support for the `Atom` editor exists,  but is deprecated since the editor will
most certainly disappear in the near future (in favor of `VS Code`).

See [atom-dedukti](https://github.com/Deducteam/atom-dedukti) for instructions
related to the `Atom` editor.

Compilation and module system
-----------------------------

Lambdapi has a (very) light module system based on file paths. Although it has
several limitations,  the module system allows the splitting developments into
several files, and even several folders. The main thing to know is that a file
holds a single module, which name corresponds to that of the file. For example
a file `nat.lp` in the working directory will define the `nat` module,  and it
can be referred as such in other files (or modules).

However, note that `nat.lp` only defines module `nat` if `lambdapi` is invoked
in the directory containing the file. Now, if the current directory contains a
directory `lib`, itself containing a file `boolean.lp`, then the corresponding
module is accessed using a full qualification `lib.boolean`. To illustrate the
behaviour of the system, consider the following example.
```bash
working_directory  # lambdapi is invoked in that directory
├── main.lp        # this module must always be refered as "main"
├── bool.lp        # this module must always be refered as "bool"
├── church
│   ├── nat.lp     # this module must always be refered as "church.nat"
│   └── list.lp    # this module must always be refered as "church.list"
└── scott
    ├── nat.lp     # this module must always be refered as "scott.list"
    └── list.lp    # this module must always be refered as "scott.list"
```
An important limitation here is the following: if `church.list` depends on the
`bool` module,  then running `lambdapi` on `list.lp` in the `church` directory
will fail. Indeed, while in that directory, the module path `bool` corresponds
to file `church/bool.lp`, which does not exist. Similarly, if `church.list` is
depending on `church.nat`, then its compilation will also fail due to the fact
that it expects to find a file `church/church/nat.lp`.

To summarize, every module path in a source tree are relative to the directory
in which `lambdapi` is invoked. Even for files in (sub-)directories. Note that
this approach allows us to easily resolve dependencies automatically. However,
we need to enforce that file paths given on the command line are normalised in
the following sense. They should not start with `./`, they should be relative,
and they should not contain `..`.
```bash
lambdapi church/nat.lp     # Correct
lambdapi ./church/nat.lp   # Incorrect
lambdapi bool.lp           # Correct
lambdapi church/../bool.lp # Incorrect
```

Syntax of Lambdapi
------------------

In this section, we will illustrate the syntax of Lambdapi using examples. The
first thing to note is that Lambdapi files are formed of a list of commands. A
command starts with a particular, reserved keyword.  And it ends either at the
start of a new command or at the end of the file.

### Lexical conventions

<!-- TODO -- >

### The `require` command

The `require` command informs the type-checker that the current module depends
on some other module, which must hence be compiled.
```
require boolean
require church.list as list
```
Note that a required module can optionally be aliased, in which case it can be
referred to with the provided name.

### The `open` command

The `open` command puts into scope the symbols defined in the given module. It
can also be combined with the `require` command.
```
open booleans
require open church.sums
```

### The `symbol` declaration command

Symbols are declared using the `symbol` command, possibly associated with some
modifier like `const` or `injective`.
```
symbol factorial : Nat ⇒ Nat
symbol add : Nat ⇒ Nat ⇒ Nat
symbol const zero : Nat
symbol const succ : Nat ⇒ Nat
```
Note that the command requires a fresh symbol name (it should not have already
been used in the current module) and a type for the symbol.

### The `rule` declaration command

Rewriting rules for definable symbols are declared using the `rule` command.
```
rule add zero      &n → &n
rule add (succ &n) &m → succ (add &n &m)
```
Note that rewriting rules can also be defined simultaneously,  using the `and`
keyword instead of the `rule` keyword for all but the first rule.
```
rule add zero      &n → &n
and  add (succ &n) &m → succ (add &n &m)
```

### The `definition` command

The `definition` command is used to immediately define a new symbol, for it to
be equal to some (closed) term.
```
definition plus_two : Nat ⇒ Nat ≔ λn,add n (succ (succ zero))
definition plus_two (n : Nat) : Nat ≔ add n (succ (succ zero))
definition plus_two (n : Nat) ≔ add n (succ (succ zero))
definition plus_two n ≔ add n (succ (succ zero))
```
Note that some type annotations can be omitted, and that it is possible to put
arguments on the left side of the `≔` symbol (similarly to a value declaration
in OCaml).

### The `theorem` command

<!-- TODO -->

### The `assert` and `assertnot` commands

The `assert` and `assertnot` are convenient for checking that the validity, or
the invalidity, of typing judgments or convertibilities.  This can be used for
unit testing of Lambdapi, with both positive and negative tests.
```
assert zero : Nat
assert add (succ zero) zero ≡ succ zero
assertnot zero ≡ succ zero
assertnot succ : Nat
```

### The `set` command

The `set` command is used to control the behaviour of Lambdapi, and to control
extension points in its syntax.  For instance,  the following commands set the
verbosity level to `1`,  enable the debugging flags `t` and `s`,  and disables
the debugging flag `s`.
```
set verbose 1
set debug +ts
set debut -s
```

The following code sets the definition of built-in symbols. They are used, for
example, to specify a zero and successor function for unary natural numbers so
that natural number literals can be automatically translated to their use.
```
set builtin "0"  ≔ zero
set builtin "+1" ≔ succ
```

The following code defines infix symbols for addition and multiplication. Both
are associative to the left, and they have priority levels `6` and `7`.
```
set infix left 6 "+" ≔ add
set infix left 7 "×" ≔ mul
```
The modifier `infix`, `infix right` and `infix left` can be used to specify
whether the defined symbol is non-associative, associative to the right,
or associative to the left. The priority levels are floating point numbers,
hence a priority can (almost) always be inserted between two different levels.

**Important limitation:** no check is done on the syntax of the symbol that is
defined. As a consequence, it is very easy to break the system by redefining a
keyword or a common symbol (e.g., `"("`, `")"` or `"symbol"`).

Interactive proof system
------------------------

<!-- TODO -->

Compatibility with Dedukti
--------------------------

One of the aims of Lambdapi is to remain compatible with Dedukti. Currently, a
second parser is included in Lambdapi in order to support the legacy syntax of
Dedukti. It should be extended whenever the syntax of Dedukti is extended, but
such changes should be discouraged.

Note that files in the legacy (Dedukti) syntax are interoperable with files in
the Lambdapi syntax. The correct parser is selected according to the extension
of files. The extension `.dk` is preserved for legacy files, and the extension
`.lp` is used for files in the Lambdapi syntax.

Although both formats are compatible, many features of Lambdapi cannot be used
from the legacy syntax. As a consequence, the use of the legacy syntax is also
discouraged.  Files can be converted from the legacy syntax to Lambdapi syntax
using the `--beautify` command line flag (see the related section).

Note that Lambdapi is able to type-check all the generated libraries that were
aimed at Dedukti (with minor modifications).  Translation scripts are provided
in the `libraries` folder and performance comparisons are given in `PERFS.md`.

Development guidelines
----------------------

Inside the repository, `lambdapi` can be compiled with the `make` command,  or
(equivalently) the `dune build` command. The generated binary files are put in
the `_build/install/default/bin` directory. This folder is automatically added
to the `PATH` when running a command with `dune exec --`. As an example, it is
possible to run `lambdapi` with the `--help` flag using the following command.
```bash
dune exec -- lambdapi --help
```

**Remark:** the `--` dune flag is necessary when calling `lambapi` with flags.
If it is not given, flags are fed to the `dune` command instead.

Repository organization
-----------------------

The root directory of the repository contains several folders:
 - `editors` holds the files related to editor support,
 - `examples` holds a bunch of examples (taken from Dedukti and new ones),
 - `libraries` holds the scripts used for checking supported libraries,
 - `lp-lsp` contains a server for the LSP protocol,
 - `proofs` holds some proofs written using tactics,
 - `src` contains the source code of Lambdapi,
 - `tests` contains test files (mostly from Dedukti),
 - `tools` contains miscellaneous utility scripts.

Profiling tools
---------------

This document explains the use of standard profiling tools for the development
of `lambdapi`.

#### Using Linux `perf`

The quickest way to obtain a per-symbol execution time is `perf`. It is simple
to use, provided that you have the right privileges on your machine. No change
is required in the build procedure, but `lambdapi` must be invoked as follows.
```bash
dune exec -- perf record lambdapi [LAMBDAPI_OPTIONS]
```
The program behaves as usual, but a trace is recorded in file `perf.data`. The
data can then be displayed with the following command.
```bash
perf report
```

#### Profiling using Gprof

The `gprof` tool can be used to obtain a more precise (and thorough) execution
trace. However, it requires modifying the `src/dune` file by replacing
```
(executable
 (name lambdapi)
```
with the following.
```
(executable
 (name lambdapi)
 (ocamlopt_flags (:standard -p))
```
This effectively adds the `-p` flag to every invocation of `ocamlopt`.

After doing that, `lambdapi` can be launched on the desired example, to record
an execution trace. This has the (side-)effect of producing a `gmon.out` file.
To retrieve the data, the following command can then be used.
```bash
gprof _build/install/default/lambdapi gmon.out > profile.txt
```
It takes two arguments: the path to the `lambdapi` binary used to generate the
profiling data, and the profiling data itself.
