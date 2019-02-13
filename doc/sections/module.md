Module system
-------------

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
