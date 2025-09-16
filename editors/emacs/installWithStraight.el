#! emacs -q --script
(load "~/.emacs.d/init.el")

(require 'straight)
(straight-use-package
 '(eglot :type git :host github :repo "joaotavora/eglot"))
(require 'eglot)
(straight-use-package
 '(highlight :type git :host github :repo "emacsmirror/highlight"))
(require 'highlight)
(straight-use-package
 '(math-symbol-lists :type git :host github :repo "vspinu/math-symbol-lists"))
(require 'math-symbol-lists)

(let ((relative-path "./lambdapi-mode-1.1.0.tar"))
  (package-install-file (expand-file-name relative-path)))

;;; :branch "release-1.6"