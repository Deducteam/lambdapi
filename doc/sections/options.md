Command line flags and tools
----------------------------

The `lambdapi` executable is the main program. It can be used to process files
written in the `lambdapi` syntax (with the ".lp" extension), and files written
in the legacy (Dedukti) syntax (with the ".dk" extension).

Run the command `lambdapi --help` to get the available options.

Several files can be given as command-line arguments, and they are all handled
independently (in the order they are given). Note that the program immediately
stops on the first failure, without going to the next file (if any).

Command line flags can be used to control the behaviour of `lambdapi`. You can
use `lambdapi --help` to get a short description of the available  flags.  The
available options are described in details below.

#### Mode selection

The `lambdapi` program may run in four modes. In the default mode, the program
parses, type-checks and handles the given files. Other modes are selected with
one of the following flags:
 - The option `--just-parse` enables the parsing mode. This means that we only
   parse the files, and print an error message in case of parse error. Even in
   parsing mode, compilation of dependencies may be triggered if corresponding
   object files are not present (this is needed for user-defined notations).
 - The option `--beautify` enables the pretty-printing mode. This mode is very
   similar to the parsing mode, but it does one more thing: the parsed data is
   printed to the standard output in `lambdapi` syntax.  This mode can be used
   for converting legacy syntax files (with the ".dk" extension) to *standard*
   syntax. Note that as for the parsing mode (`--justparse` flag), compilation
   of dependencies may be triggered.
 - The option `--lsp-server` runs the Lambdapi LSP server. In this case, there
   should be no source files given as argument.

Note that when several mode selection flags are given,  only the latest one is
taken into account. Moreover, some command-line flags may be ignored (the help
flags `--help` and `-help` are always active).

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

#### File path options

The following options can be used to configure the module and package system:
 - `--lib-root <DIR>` sets the library root, that is, the folder corresponding
   to the entry point of the Lambdapi package system. This is the folder under
   which every package is installed, and a default value is only only known if
   Lambdapi has been installed. In development mode,  `--lib-root lib` must be
   given (assuming Lambdapi is run at the root of the repository).
 - `--map <MOD_PATH>:<DIR>` maps an arbitrary directory `<DIR>` under a module
   path `<MOD_PATH>` (relative to the root directory).  This  option is useful
   during the development of a package (before it has been installed). However
   it can also be accessed using a package configuration file (`lambdapi.pkg`)
   at the root of the library's source tree. More information on that is given
   in the section about the module system.

#### Server mode flags

The following options can be used in server mode (`--lsp-server` flag):
 - `--standard-lsp` restricts to standard LSP protocol (no extension).
 - `--lsp-log-file <file>` sets the log file for the LSP server. If not given,
   the file `/tmp/lambdapi_lsp_log.txt` is used.
