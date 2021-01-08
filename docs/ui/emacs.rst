.. _editing-lambdapi-source-code-with-emacs-melpamelpa-badgemelpa-link:

Emacs
=====
`MELPA <https://melpa.org/#/lambdapi-mode>`_

Lambdapi source code can be edited with the `emacs`_ editor with the major
mode ``lambdapi-mode``. It requires Emacs 26.1 or higher and provides:

* Syntax highlighting for Lambdapi (``*.lp`` files) and Dedukti2 (``*.dk``
  files)
* Auto indentation for Lambdapi
* Easier unicode input
* Completion for Lambdapi
* Typing of symbol at point (in minibuffer)
* Type checking declarations

Installation
------------

The ``lambdapi-mode`` is automatically installed when using ``opam``
(provided that emacs is available at installation time). It can be also
be installed from the sources and from `MELPA <https://melpa.org>`__
using any package manager of Emacs (``package.el``,
`straight <https://github.com/raxod502/straight.el>`__, …). Installation
from opam or the sources requires less configuration on the Emacs side,
but installation through Melpa takes care automatically of dependencies.

Installing with `opam`_:
  opam installs both lambdapi and the emacs mode. So if lambdapi has been
  installed using opam, the lambdapi-mode should be as well. If it is not the
  case, it may still be installed using one of the other two installation
  methods. To activate the mode when editing ``.lp`` and ``.dk`` files, add to
  the configuration file of Emacs (``~/.emacs.d/init.el`` or ``~/.emacs``):

  .. code:: emacs-lisp

     (load "lambdapi-site-file")

  If Emacs fails on startup with the following message:

     ``Cannot open load file: No such file or directory, lambdapi-site-file``

  then you have to add the folder containing the emacs-lisp files to the load
  path of Emacs. For this, there are two options

  * `opam`_ (or rather
    `opam-user-setup <https://github.com/OCamlPro/opam-user-setup>`_)
    can set that up for you with ``opam user-setup install``
  * it can be done manually, editing Emacs’ configuration file, adding *before*
    ``(load "lambdapi-site-file")``

    .. code:: emacs-lisp

       (require 'subr-x)
       (let* ((opshare (shell-command-to-string "opam var share"))
              (opshare (string-trim opshare)))
         (add-to-list 'load-path (concat opshare "/emacs/site-lisp/")))

  The ``opam`` installation does not handle dependencies. The following
  packages might be missing (available on `elpa`_):

  * `eglot`_,
  * `highlight`_,
  * `math-symbol-lists`_,
  * `company`_ (optional) for tooltip unicode completion,
  * `company-math`_ (optional) for tooltip unicode completion).

Installing from sources:
  the lambdapi emacs mode can be installed
  from the sources:

  .. code:: shell

     cd lambdapi
     make install_emacs

  This command will byte-compile a file using the emacs binary available
  in the path. The ``EMACS`` variable of the makefile can be modified to
  specify which emacs binary is to be used. The configuration steps are
  the same as for the installation with opam.

Installing from MELPA:
  provided that Emacs is properly configured
  (or see https://melpa.org/#/getting-started to configure
  Emacs to use MELPA), the mode can be installed with
  ``M-x package-install RET lambdapi-mode``.

  If you have `use-package`_, it can be automatically installed by adding to
  your configuration file:

  .. code:: emacs-lisp

     (use-package lambdapi-mode)

Usage
-----

Commenting regions
^^^^^^^^^^^^^^^^^^

Lambdapi handles only single-line comments with ``//``. To comment a
region in Emacs, select it and use ``M-;``.

Entering unicode
^^^^^^^^^^^^^^^^

Company:
  if `company`_ and `company-math`_ are installed, LaTeX commands are
  autocompleted with the latter tool. Any (or at least a lot of) LaTeX symbol
  can be entered via its LaTeX command: start typing it, and an autocompletion
  tooltip should suggest the unicode symbol.

  This method is the more complete and easier to use, but depends on
  ``company``.

LambdaPi input method:
  if `company`_ or `company-math`_ is not installed, LaTeX characters can be
  entered via the LambdaPi input method. Greek characters can be accessed using
  backquoted letters (as done in `cdlatex`_), or with the LaTeX command: α can
  be accessed with :literal:`\`a` or ``\alpha``, β with :literal:`\`b` or
  ``\beta``, and similarly for other Greek letters.

*NOTE on the interaction between the input method and company:* the
dropdown window of company-math will not appear as long as the current
word is a candidate for a completion of the input method. To favour
company over the input method, the input method can be disabled setting
the variable ``lambdapi-unicode-prefer-company`` to a non-nil value in
``~/.emacs`` or ``~/.emacs.d/init.el``:

.. code:: emacs-lisp

   (setq lambdapi-unicode-prefer-company 1)

abbrev mode:
  the ``abbrev`` mode is an emacs minor mode allowing the user to define
  abbreviations. For instance, one may define “btw” to be an abbreviation of “by
  the way” with, ``add-global-abbrev``. Doing so will cause the sequence “btw”
  to be automatically expanded when the user hits ``SPC`` or ``TAB``. The
  expansion can be inhibited by hitting ``C-q`` before ``SPC``.

  The function ``lambdapi-local-abbrev`` can be called when the cursor is at the
  end of a word to define the word as an abbreviation. When called, the user can
  input the expanded form in the minibuffer. Additionnally, the abbreviation is
  added as a directory local variable, so it will be available the next time a
  file of the project is opened. The function ``lambdapi-local-abbrev`` is bound
  to ``C-c a``.

  To enter unicode characters in the minibuffer using LaTeX, the TeX input
  method can be used, for this, once in the minibuffer, enter ``C-x RET C-\``
  and select ``TeX`` in the list.

LSP server
^^^^^^^^^^

Navigating goals
''''''''''''''''

On lambdapi-mode startup, a window showing the goals at the current line
is open.

You can toggle the interactive mode with ``C-c C-i``. If you were to do
so, you still can navigate the proofs with ``C-c C-p`` and ``C-c C-n``,
jump between proofs with ``C-c C-b`` and ``C-c C-f``, and show the goals
at the current line with ``C-c C-c``. As always with emacs, if you were
to be dissatisfied with these keybindings, you can change them easily!

Clicking on the ``i``-th goal of the ``*Goals*`` buffer puts the focus on it
by inserting a ``focus i`` tactic in the proof script.

CPU usage and deactivation
''''''''''''''''''''''''''

If for any reason the LSP server consumes too much power (e.g. if a
non-terminating rewrite system is edited), it can be disabled with
``M-x eglot-shutdown``.

Pseudo interactive proof mode
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

One can use `quickrun`_ to call lambdapi while editing a buffer. It can be
configured for lambdapi with

.. code:: emacs-lisp

   (quickrun-add-command "lambdapi"
     '((:command . "lambdapi check")
       (:exec    . ("%c %s")))
     :mode 'lambdapi-mode)
   (add-hook 'lambdapi-mode-hook
     (lambda () (define-key lambdapi-mode-map (kbd "C-c r") #'quickrun)))

to run lambdapi on the edited buffer with ``C-c r``. It can be used to
display goals while doing a proof. To display the result of ``compute``,
``type``, and simlar commmand as well, write ``"%c --verbose 1 %s"``
instead of ``"%c %s"``.


Customize window layout
'''''''''''''''''''''''
The window layout can be customized in the LambdaPi customization group
(Do ``M-x customize-group lambdapi``).
The layout can be refreshed with ``C-c C-r``.


Other relevant packages
-----------------------

* `company`_: auto-completion
* `company-math`_: unicode symbols auto completion
* `unicode-fonts <https://github.com/rolandwalker/unicode-fonts>`__: to
  configure correctly Emacs’ unicode fonts
* `rainbow-delimiters <https://github.com/Fanael/rainbow-delimiters>`__:
  to appreciate having a lot of parentheses
* paredit: to help keeping the parentheses balanced
* `quickrun`_: for code evaluation

To have everything configured using `use-package`_, use

.. code:: emacs-lisp

   (use-package lambdapi-mode
       :hook (paredit-mode rainbow-delimiters-mode-enable))

.. _elpa: https://elpa.gnu.org
.. _eglot: https://github.com/joaotavora/eglot
.. _company: http://company-mode.github.io
.. _company-math: https://github.com/vspinu/company-math
.. _use-package: https://github.com/jwiegley/use-package
.. _cdlatex: https://www.gnu.org/software/emacs/manual/html_node/org/CDLaTeX-mode.html
.. _quickrun: https://github.com/emacsorphanage/quickrun
.. _emacs: https://www.gnu.org/software/emacs/
.. _opam: http://opam.ocaml.org
.. _highlight: https://www.emacswiki.org/emacs/HighlightLibrary
.. _math-symbol-lists: https://elpa.gnu.org/packages/math-symbol-lists.html
