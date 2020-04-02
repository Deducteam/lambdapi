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

Entering unicode
----------------
To enter unicode characters, there are several options. 

### The `LambdaPi` input method
LaTeX characters can be entered via the input method. Bindings come from 
[`cdlatex`](https://www.gnu.org/software/emacs/manual/html_node/org/CDLaTeX-mode.html),
that is, α can be accessed with `\`a`, β with `\``, &c. This method has the
advantage of being lightweight and easy to use, but is not extensible.

### The `abbrev` mode
The `abbrev` mode is an emacs minor mode allowing the user to define
abbreviations. The function `lambdapi-local-abbrev` can be called when the
cursor is at the end of a word to define the word as an abbreviation. When
called, the user can input the expanded form in the minibuffer. Additionnally,
the abbreviation is added as a directory local variable, so it will be available
the next time a file of the project is opened. The function
`lambdapi-local-abbrev` is bound to `C-c a`.

To enter unicode characters in the minibuffer using LaTeX, the TeX input method
can be used, for this, once in the minibuffer, enter `C-x RET C-\\` and select
`TeX` in the list.

Other relevant packages
-----------------------
* [company-mode](https://github.com/company-mode/company-mode): auto-completion
* [company-math](https://github.com/vspinu/company-math): unicode symbols auto
  completion

The author thanks the [nim-mode](https://github.com/nim-lang/nim-mode) for
serving as template for the development of several parts of this mode.
