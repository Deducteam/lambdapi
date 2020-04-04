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
In the long term, the package should be available on MELPA, and only `M-x
package-install RET lambdapi-mode` should then be necessary.

Meanwhile, the package archive can be generated with 
`make dist` and `make install`.

Remove with `package-delete RET lambdapi-mode`.

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
