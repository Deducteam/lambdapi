Getting started
===============

This guide is intended for anyone wishing to give Lambdapi a try, but
also for everyone that wants to get started with the development of a
new library in the system. The first thing to know is that Lambdapi
deliberately enforces a strict discipline on file and module management
(more details on that in later sections). As a consequence, it is not in
general possible to run ``lambdapi`` on a source file directly. In
particular, actions must be taken so that the system knows where, in the
global module hierarchy, a given module (or source file) should be
placed. This may seem like a strong restriction, but this will allow us
to develop simple, well-integrated and powerful tooling in the future
(including a proper build system and a package manager).

Note however that we provide tools to hide as much of the restriction to
the user as possible.

Creating a new package
----------------------

The very first thing to do to start using Lambdapi, assuming it has
already been installed on your system, is to create a new **Lambdapi
package**. Every source file must be part of some package in Lambdapi,
and this package will determine the name space under which the objects
of the package will be made accessible to other objects of the package,
but also to other libraries if the package is ever installed. It is
hence important to choose an appropriate name for the packages you
create. In particular, this name should uniquely identify the package as
it will never be possible to install two distinct packages with the same
name.

**To create your first package**, simply run
``lambdapi init my_package``. The effect of this command is to create a
new directory ``my_package`` containing several generated files,
including a ``Makefile`` and a Lambdapi package file ``lambdapi.pkg``,
but also a somewhat minimal example of Lambdapi project containing
several source files with the ``.lp`` extension. After entering the new
directory, you can run the ``make`` command to build the object files of
the package. And you can then start working on your project by modifying
and creating new source files by running ``make`` again to type-check
and run the commands they contain. Note that dependencies are handled
automatically, and that every file having the ``.lp`` extension in the
repository is considered to be part of the package.

When creating a package, it is also possible to specify a module path
under which the package should be placed:
``lambdapi init contrib.libs.my_package``. In that case, the name of
your package (and of the created folder) is still ``my_package``, but
every object defined in the package will be accessed with a module path
prefixed with ``contrib.libs.my_package`` instead of ``my_package``
only. This allows for a more fine-grained management of name spaces.

**TL;DR**

.. code:: bash

   lambdapi init my_package # Create a new package "my_package".
   cd my_package            # Move to the created directory.
   make                     # Build the example project.

Subdirectories and module hierarchy
-----------------------------------

Every file with the ``.lp`` extension under a package’s directory is
considered to be part of the package. In particular, files can be
classified into several directories and subdirectories. However, it is
important to note that the directory structure is reflected into the way
objects are qualified. As an example, the objects defined in file
``dir1/dir2/file.lp`` will be accessible in any other module with the
qualification ``my_packake.dir1.dir2.file`` (or
``contrib.libs.my_package.dir1.dir2.file`` if the package is placed
under the more complex module path discussed in the previous section).
Note that this implies that the same qualification will be used in other
modules of the same package, but also (after installation) in the
modules of another packages that depend on your package.

**As an exercise**, move the example file ``nat.lp`` (included in your
freshly generated package) to ``internal/nat.lp``. If you then try to
run ``make`` the command will fail (try it!). Indeed, since the source
file ``nat.lp`` has moved, its module path has changed accordingly. Now
try and fix the problem until the ``make`` command succeeds again at
compiling ``main.lp``.

Experimenting with the system
-----------------------------

While you keep reading the following sections of this manual, we
encourage you to experiment with the system. You can do that by creating
new files in your test package, and using ``make`` to type-check them.
Note that by default the system will not give you much feedback.
However, once you are editing files in a package (i.e., when there is a
``lambdapi.pkg`` file available in a parent directory of the files you
consider), you can very well call Lambdapi directly (i.e., without
relying on the ``Makefile``). For example, you can try running the
command ``lambdapi check --recompile --verbose 4 internal/nat.lp``. As
you are introduced to new commands (or discover them), feel free to try
them out.

**Note:** do not hesitate to report any problem you may have using our
`issue tracker <https://github.com/Deducteam/lambdapi/issues>`_.

Installing a package
--------------------

Packages must be installed following specific conventions, and hence
this should not be attempted directly. Instead, we provide a
``lambdapi install`` command that takes care of installing the source
and object files it is given as argument in the right place, according
to the package file. The ``Makefile`` that is generated at package
creation time comes with an ``install`` target, so installing your
package is as simple as running ``make install``. Of course, you can
also uninstall your package using the command ``make uninstall``.
