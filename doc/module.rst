Module system
=============

Lambdapi has a light module system based on file paths. It allows
you to split your developments across files and folders.
The main thing to know is that a file holds a single module,
and accessing this module in other files requires using its *full*
module path.

Module path
-----------

The module path that corresponds to a source file is defined using the
name of the file, but also the position of the file under the *library
root* (a folder under which all libraries are installed).

By default, the library root is ``/usr/local/lib/lambdapi/lib_root`` or
``$OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root`` if ``OPAM_SWITCH_PREFIX``
is defined. An alternative library root can be specified using the environment
variable ``LAMBDAPI_LIB_ROOT`` or the :doc:`command line flag <options>`
``--lib-root``.

The typical case is when we want to access a module of some installed
library. In that case, the module path
is built using the file path as follows: if the source file is at
``<LIB_ROOT>/std/bool.lp``, it is accessed with module path ``std.bool``.
And if there are nested folders then the module path gets more members.
File ``<LIB_ROOT>/std/a/b/c/d.lp`` has module path ``std.a.b.c.d``.

*By default, all modules are looked up under the library root*. However,
there are cases where the files we want to work with are not yet
placed under the library root. The typical case is when a library is
under development. In that case, the development folder can
be mapped under the library root, similarly to what would
happen when mounting a volume in a file system. There are two ways of
doing that, the first one is to use the ``--map-dir MOD:DIR``
:doc:`command line option </options>`.
However, the best way is to use a package configuration file.

Package configuration file
--------------------------

A package configuration file ``lambdapi.pkg`` can be placed at the root of the
source tree of a library under development.
It must contain the following fields (an example is given below for the syntax):

* ``package_name`` giving a globally unique name for the package being defined.
  This is not used yet, but will be necessary when packages will eventually
  be published online so that they can be automatically downloaded when users
  (the idea is to come up with a system similar to Cargo in Rust).

* ``root_path`` gives the module path under which the library is to be placed.
  Assuming that our configuration file is at ``<REPO_ROOT>/lambdapi.pkg``, this
  means that ``<REPO_ROOT>/a/b/c.lp`` will get module path
  ``<ROOT_PATH>.a.b.c``. In other words, this is equivalent to ``--map-dir
  <ROOT_PATH>:<REPO_ROOT>`` on the command line.

Remark: `.lpo` files needs to be removed and regenerated if the
root_path is changed.

In the future, more useful meta data may be added to the configuration
file, for example the name of the author, the version number, the dependencies,
…

Example of configuration file (syntax reference):

::

   # Lines whose first non-whitespace charater is # are comments  
   # The end of a non-comment line cannot be commented.
   # The config file MUST be called "lambdapi.pkg".
   # The syntax for entries is:
   key = value
   # If the key is not known then it is ignored.
   # There are two used keys for now:
   package_name = my_package_name
   root_path    = a.b.c
   # We will use more entries later (e.g., authors, version, ...)

Installation procedure for third-party packages
-----------------------------------------------

A package should be installed under the library directory, under the
specified root path. In other words a package whose root path is
``x.y.z`` should have its files installed under the directory
``<LIB_ROOT>/x/y/z``. Moreover the directory structure relative to the
package configuration file should be preserved.

Of course, we should enforce that a root path is uniquely used by one
package. This can be enforced using a central authority, but this can
only be done when we actually decide to implement automatic package
distribution. For now, it is assumed that every user uses reasonable
root paths for their packages.

Note that if a package uses root path ``a.b.c`` then no other package
should use root path ``a`` or ``a.b`` (and obviously not ``a.b.c``
either). However there is no problem in using ``a.d`` or ``a.b.d``. The
rules are as follows:

* the root path of a package cannot be a prefix of the root path of another,

* the root path of a package cannot extend the root path of another.

We will use the following conventions:

* root path ``std`` is reserved for the standard library,

* extracted libraries are installed under ``libraries.<NAME>`` (for example, we
  would use root path ``libraries.matita`` for ``matita``).
