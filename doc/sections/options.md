Command line flags and tools
----------------------------

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
treatment of [modules](doc/modules.md).

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
