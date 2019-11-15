Command line flags and tools
----------------------------

The `lambdapi` executable is the main program. It can be used to process files
written in the `lambdapi` syntax (with the ".lp" extension), and files written
in the legacy (Dedukti) syntax (with the ".dk" extension).

Run the command `lambdapi --help` to get the available options.

Several files can be given as command-line arguments, and they are all handled
independently (in the order they are given). Note that the program immediately
stops on the first failure, without going to the next file (if any).

**Important note:** the paths given on the command-line for input files should
be relative to the current directory. Moreover, they should neither start with
the `./` current directory marker, nor contain the parent directory marker
`../`. This is due to the fact that the directory structure is significant due
to the treatment of [modules](module.md).

Command line flags can be used to control the behaviour of `lambdapi`. You can
use `lambdapi --help` to get a short description of the available flags.  The
available options are described in details below.

#### Mode selection

The `lambdapi` program may run in three different modes. The standard mode (it
is selected by default) parses, type-checks and handles the given files. Other
modes are selected with one of the following flags:
 - `--just-parse` enables the parsing mode: the files are parsed and `lambdapi`
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

Lambdapi provides an option to check the confluence of the set of rewriting
rules declared in a file by calling external provers using the [TRS format]
(http://project-coco.uibk.ac.at/problems/trs.php).
The `--confluence <cmd>` flag specifies the confluence-checking command to  be
used. The command is expected to behave as follows:
 - take the problem description (in `.trs` format) on its standard input,
 - output on its first line either `YES`, `NO` or `MAYBE`.

As an example,  `echo MAYBE` is the simplest possible (valid) confluence-check
that one may use.

For now, only the [`CSI^ho` confluence checker]
(http://cl-informatik.uibk.ac.at/software/csi/ho/) has been tested with
`lambdapi`.
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

Lambdapi provides an option to check the termination of the set of rewriting
rules declared in a file by calling external provers using the [XTC format]
(http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB/raw-file/tip/xml/xtc.xsd).
The `--termination <cmd>` flag specifies the termination-checking command to
be used. The command is expected to behave as follows:
 - take the problem description (in `.xml` format) on its standard input,
 - output on its first line either `YES`, `NO` or `MAYBE`.

As an example,  `echo MAYBE` is the simplest possible (valid)
termination-check that one may use.

As far as we know,
[`SizeChangeTool`](https://github.com/Deducteam/SizeChangeTool) is the
only termination checker compatible with all `lambdapi` features.
It can be called in the following way.
```bash
lambdapi --termination "path/to/sct.native --no-color --stdin=xml" input_file.lp
```

If the file does not contain type-level rewriting,
[`Wanda`](http://wandahot.sourceforge.net/) is also compatible.
However, it does not offer the possibility to give an input in `stdin`.

To generate the `.xml` file corresponding to some `lambdapi` file, one may use
a dummy termination-checking command as follows.
```bash
lambdapi --termination "cat > output.trs; echo MAYBE" input_file.lp
```

#### Debugging flags

The following flags may be useful for debugging:
 - `--debug <flags>` enables the debugging modes specified by every character of
   `<flags>`. Details on available character flags are obtained using
   the `--help` flag.
 - `--timeout <int>` gives up type-checking after the given number of seconds.
   Note that the timeout is reset between each file, and that the parameter of
   the command is expected to be a natural number.
 - `--too-long <float>` gives a warning for each command (i.e., file item) taking
   more than the given number of seconds to be checked. The given parameter is
   expected to be a floating point number.

#### Rewriting engine

The following options can be used to modify the behaviour of the
reduction engine,
 - `--write-trees` writes the decision trees used for rule filtering
   to dot files; for each symbol `s`, a file `mod_path/mod_name.s.gv` is
   generated. For more information on trees (and how to read them), see
   `src/tree_graphviz.ml`.
 - `--keep-rule-order` forces the rewriting engine to use in priority
   the topmost rules.
