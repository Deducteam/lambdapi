`lambdapi-mode` a major mode for editing lambdapi code
=======================================================

This packages provides (with Emacs 24 or higher):
* Syntax highlighting for Lambdapi (`*.lp` files) and Dedukti2 (`*.dk` files)
* Auto indentation for Lambdapi
* Completion for Lambdapi

and with LSP, `eglot` (and Emacs 26.1 or higher):
* Typing of symbol at point (in minibuffer)
* Type checking declarations

Installation
------------
If you installed `lambdapi`, then the mode is already installed. To activate it
upon opening `.lp` files, add to your `~/.emacs.d/init.el` or `~/.emacs`
``` emacs-lisp
(require 'subr-x)
(let* ((opshare (shell-command-to-string "opam var share"))
       (opshare (string-trim opshare)))
  (add-to-list 'load-path (concat opshare "/emacs/site-lisp/")))
(load "lambdapi-site-file")
```
Installation via Dune does not handle dependencies, so afterwards, install
through emacs (all packages are available on [`elpa`](https://elpa.gnu.org)):
- [`eglot`](https://github.com/joaotavora/eglot),
- [`company`](http://company-mode.github.io/) (optional, for tooltip unicode
  completion),
- [`company-math`](https://github.com/vspinu/company-math) (optional, for
  tooltip unicode completion).

The package can also be installed via the Emacs package manager, run
`M-x package-install RET lambdapi-mode`. If you have
[`use-package`](https://github.com/jwiegley/use-package), add
``` emacs-lisp
(use-package lambdapi-mode)
```

Entering unicode
----------------
**Company:**
if [`company-mode`](https://github.com/company-mode/company-mode) and
[`company-math`](https://github.com/vspinu/company-math) are installed, 
LaTeX commands are autocompleted with the latter tool. Any (or at least a lot
of) LaTeX symbol can be entered via its LaTeX command: start typing it, and an
autocompletion tooltip should suggest the unicode symbol.

This method is the more complete and easier to use, but depends on `company`.

**`LambdaPi` input method:**
if `company` or `company-math` is not installed, LaTeX characters can be entered
via the `LambdaPi` input method. Greek characters can be accessed using
backquoted letters (as done in
[`cdlatex`](https://www.gnu.org/software/emacs/manual/html_node/org/CDLaTeX-mode.html)
), or with the LaTeX command: α can be accessed with `` `a `` or `\alpha`, β
with `` `b `` or `\beta` &c.

**`abbrev` mode:**
the `abbrev` mode is an emacs minor mode allowing the user to define
abbreviations. For instance, one may define "btw" to be an abbreviation of "by
the way" with, `add-global-abbrev`. Doing so will cause the sequence "btw" to be
automatically expanded when the user hits `SPC` or `TAB`. The expansion can be
inhibited by hitting `C-q` before `SPC`.

The function `lambdapi-local-abbrev` can be called when the
cursor is at the end of a word to define the word as an abbreviation. When
called, the user can input the expanded form in the minibuffer. Additionnally,
the abbreviation is added as a directory local variable, so it will be available
the next time a file of the project is opened. The function
`lambdapi-local-abbrev` is bound to `C-c a`.

To enter unicode characters in the minibuffer using LaTeX, the TeX input method
can be used, for this, once in the minibuffer, enter `C-x RET C-\` and select
`TeX` in the list.

Other relevant packages
-----------------------
* [company-mode](https://github.com/company-mode/company-mode): auto-completion
* [company-math](https://github.com/vspinu/company-math): unicode symbols auto
  completion
* [unicode-fonts](https://github.com/rolandwalker/unicode-fonts): to configure
  correctly Emacs' unicode fonts
* `paredit.el`: to help keeping the parentheses balanced
