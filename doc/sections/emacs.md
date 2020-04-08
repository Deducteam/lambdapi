Editing lambdapi source code with Emacs
---------------------------------------

Lambdapi source code can be edited with the
[Emacs](https://www.gnu.org/software/emacs/) editor with the major mode
`lambdapi-mode`. It requires Emacs 26.1 or higher and provides:
* Syntax highlighting for Lambdapi (`*.lp` files) and Dedukti2 (`*.dk` files)
* Auto indentation for Lambdapi
* Easier unicode input
* Completion for Lambdapi
* Typing of symbol at point (in minibuffer)
* Type checking declarations

### Installation
The `lambdapi-mode` can be installed with `opam` or with the package manager of
Emacs through [MELPA](https://melpa.org).

**Installing with `opam`:** the emacs mode is installed simultaneously with
`lambdapi`, so if `lambdapi` has been installed, so is the `lambdapi-mode`. To
activate the mode when editing `.lp` and `.dk` files, add to the configuration
file of Emacs (`~/.emacs.d/init.el` or `~/.emacs`):
``` emacs-lisp
(load "lambdapi-site-file")
```
If Emacs fails on startup with the following message:

> `Cannot open load file: No such file or directory, lambdapi-site-file`

then you have to add the folder containing the emacs-lisp files to the load path
of Emacs. For this, there are two options
* `opam` (or rather
  [`opam-user-setup`](https://github.com/OCamlPro/opam-user-setup)) can set that
  up for you with `opam user-setup install`
* it can be done manually, editing Emacs' configuration file, adding *before*
  `(load "lambdapi-site-file")`
  ``` emacs-lisp
  (require 'subr-x)
  (let* ((opshare (shell-command-to-string "opam var share"))
         (opshare (string-trim opshare)))
    (add-to-list 'load-path (concat opshare "/emacs/site-lisp/")))
  ```

The `opam` installation does not handle dependencies. The following packages
might be missing (available on [`elpa`](https://elpa.gnu.org)):
- [`eglot`](https://github.com/joaotavora/eglot),
- [`company`](http://company-mode.github.io/) (optional, for tooltip unicode
  completion),
- [`company-math`](https://github.com/vspinu/company-math) (optional, for
  tooltip unicode completion).
  
**Installing from MELPA:** provided that Emacs is properly configured (or see
[here](https://melpa.org/#/getting-started) to configure Emacs to use MELPA),
the mode can be installed with `M-x package-install RET lambdapi-mode`.

If you have [`use-package`](https://github.com/jwiegley/use-package), it can be
automatically installed by adding to your configuration file:
```emacs-lisp
(use-package lambdapi-mode)
```

### Usage

#### Commenting regions 
`lambdapi` handles only single-line comments with `//`. To comment a region in
Emacs, select it and use `M-;`.

#### Entering unicode
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

To force using the input method rather than `company`, set the variable
`lambdapi-unicode-force-quail` to a non-nil value in `~/.emacs` or
`~/.emacs.d/init.el`:
``` emacs-lisp
(setq lambdapi-unicode-force-quail 1)
```

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

#### LSP server
If for any reason the LSP server consumes too much power (e.g. if a
non-terminating rewrite system is edited), it can be disabled with
`M-x eglot-shutdown`.

#### Pseudo interactive proof mode
One can use [`quickrun.el`](https://github.com/emacsorphanage/quickrun) to call
lambdapi while editing a buffer. It can be configured for lambdapi with
```emacs-lisp
(quickrun-add-command "lambdapi"
  '((:command . "lambdapi check")
    (:exec    . ("%c %s")))
  :mode 'lambdapi-mode)
(define-key lambdapi-mode-map (kbd "C-c r") #'quickrun)
```
to run lambdapi on the edited buffer with `C-c r`. It can be handful to display
goals while doing a proof.

### Other relevant packages
* [company-mode](https://github.com/company-mode/company-mode): auto-completion
* [company-math](https://github.com/vspinu/company-math): unicode symbols auto
  completion
* [unicode-fonts](https://github.com/rolandwalker/unicode-fonts): to configure
  correctly Emacs' unicode fonts
* [rainbow-delimiters](https://github.com/Fanael/rainbow-delimiters): to
  appreciate having a lot of parentheses
* `paredit.el`: to help keeping the parentheses balanced
* [`quickrun.el`](https://github.com/emacsorphanage/quickrun): for code 
  evaluation

To have everything configured using `use-package`, use
```emacs-lisp
(use-package lambdapi-mode
    :hook (paredit-mode rainbow-delimiters-mode-enable))
```
