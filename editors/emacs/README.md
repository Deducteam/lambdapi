`lambdapi-mode`, a major mode for editing lambdapi code
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

Other relevant packages
-----------------------
* [company-mode](https://github.com/company-mode/company-mode): auto-completion

The author thanks the [nim-mode](https://github.com/nim-lang/nim-mode) for
serving as template for the development of several parts of this mode.
