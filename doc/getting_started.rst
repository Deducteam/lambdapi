Getting started
===============

The very first thing to do to start using Lambdapi, assuming it has
already been installed on your system, is to create a new **Lambdapi
package**. Every source file must be part of some package, and this
package will determine the name space under which the objects of the
package will be made accessible to other objects of the package, but
also to other libraries if the package is ever installed and used by
others.

**To create your first package**, create a new directory for your
package and simply run ``lambdapi init my_root_path`` in it. This
command creates in the current directory a Lambdapi package file
``lambdapi.pkg`` and a ``Makefile`` to check and (un)install the
Lambdapi files that are in the directory and its sub-directories.

**TL;DR**

.. code:: bash

   mkdir my_package         # Create a directory for my package.
   cd my_package            # Move to the created directory.
   lambdapi init my_package # Create "lambdapi.pkg" and "Makefile".
   make                     # Check the lambdapi files.
   make install             # Install them in the system library.

To use in ``./file2.lp`` a symbol ``f`` declared in
``./subdir/file1.lp``, one simply needs to write in ``./file2.lp``:

.. code:: lambdapi

          require my_root_path.subdir.file1;
          // my_root_path.subdir.f is now available
          open my_root_path.subdir.file1;
          // f now refers to my_root_path.subdir.f

Note that the root path of the package can be a hierarchical name like
``my.root.path``. This allows for a more fine-grained management of
name spaces.

For more details on the contents on ``lambdapi.pkg`` and the module
system, see :ref:`<module>`.
