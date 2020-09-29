;; -*- lexical-binding: t; -*-
;;
;;  Serves as site-file.el, that is, if `lambdapi-mode' is not installed through
;;  melpa, this file should be loaded explicitly to replace the autoloads.
;;

(autoload 'lambdapi-legacy-mode "lambdapi-mode"
  "A mode for editing LambdaPi files (in legacy syntax)." t nil)
(add-to-list 'auto-mode-alist '("\\.dk\\'" . lambdapi-legacy-mode))

(autoload 'lambdapi-mode "lambdapi-mode"
  "A mode for editing LambdaPi files." t nil)
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))

(autoload 'lambdapi-completion-at-point "lambdapi-capf"
  "Completion of symbol at point for lambdapi." t nil)
