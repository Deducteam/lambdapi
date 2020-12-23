;;; lambdapi-mode.el --- A major mode for editing Lambdapi source code -*- lexical-binding: t; -*-

;; Copyright (C) 2020 Deducteam

;; Author: Rodolphe Lepigre, Gabriel Hondet
;; Maintainer: Deducteam <dedukti-dev@inria.fr>
;; Version: 1.0
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
;; Homepage: https://github.com/Deducteam/lambdapi
;; Keywords: languages
;; Compatibility: GNU Emacs 26.1
;; Package-Requires: ((emacs "26.1") (eglot "1.5") (math-symbol-lists "1.2.1") (highlight "20190710.1527"))

;;; Commentary:

;;  A major mode for editing Lambdapi source code. This major mode provides
;;  indentation, syntax highlighting, completion, easy unicode input, and more.

;;; Code:

(require 'eglot)
(require 'lambdapi-vars)
(require 'lambdapi-smie)
(require 'lambdapi-capf)
(require 'lambdapi-abbrev)
(require 'lambdapi-input)
(require 'lambdapi-proofs)
;;; Legacy
;; Syntax table (legacy syntax)
(defvar lambdapi-mode-legacy-syntax-table nil "Syntax table for LambdaPi.")

(setq lambdapi-mode-legacy-syntax-table
  (let ((syn-table (make-syntax-table)))
    (modify-syntax-entry ?\( "()1n" syn-table)
    (modify-syntax-entry ?\) ")(4n" syn-table)
    (modify-syntax-entry ?\; ". 23" syn-table)
    syn-table))

;; Keywords (legacy syntax)
(defconst lambdapi-legacy-font-lock-keywords
  (list
   (cons
    (concat
     "\\<"
     (regexp-opt '("def" "thm" "inj"))
     "\\>") 'font-lock-keyword-face)
   (cons
    (concat
     "#"
     (regexp-opt '("REQUIRE" "EVAL" "INFER" "ASSERT" "ASSERTNOT"))
     "\\>") 'font-lock-preprocessor-face))
  "Keyword highlighting for the LambdaPi mode (legacy syntax).")


;; Main function creating the mode (legacy syntax)
;;;###autoload
(define-derived-mode lambdapi-legacy-mode prog-mode "LambdaPi (legacy)"
  "A mode for editing LambdaPi files (in legacy syntax)."
  (set-syntax-table lambdapi-mode-legacy-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-legacy-font-lock-keywords))
  (setq-local comment-start "(;")
  (setq-local comment-end ";)")
  (setq-default indent-tabs-mode nil)
  (add-to-list 'eglot-server-programs
               '(lambdapi-legacy-mode . ("lambdapi" "lsp" "--standard-lsp")))
  (eglot-ensure))

(provide 'lambdapi-legacy-mode)

;;; lambdapi
;; Keywords
(defconst lambdapi-font-lock-keywords
  (list (cons
         (concat "\\<" (regexp-opt lambdapi-sig-commands) "\\>")
         'font-lock-keyword-face)
        (cons
         (concat "\\<" (regexp-opt lambdapi-misc-commands) "\\>")
         'font-lock-preprocessor-face)
        (cons
         (concat "\\<" (regexp-opt lambdapi-tactics) "\\>")
         'font-lock-builtin-face)
        (cons
         (concat "\\<" (regexp-opt lambdapi-warning) "\\>")
         'font-lock-warning-face)
        (cons
         (concat "\\<" (regexp-opt lambdapi-misc-keywords) "\\>")
         'font-lock-constant-face))
  "Keyword highlighting for the LambdaPi mode.")

;; Hook to be run when changing line
;; From https://emacs.stackexchange.com/questions/46081/hook-when-line-number-changes
(defvar lambdapi-current-line-number (line-number-at-pos))
(defvar lambdapi-changed-line-hook nil)

(defun lambdapi-update-line-number ()
  (if interactive-goals
      (let ((new-line-number (line-number-at-pos)))
        (when (not (equal new-line-number lambdapi-current-line-number))
          (setq lambdapi-current-line-number new-line-number)
          (run-hooks 'changed-line-hook)))))

(defun lambdapi-create-goals-buffer ()
  (let ((goalsbuf (get-buffer-create "*Goals*"))
        (goalswindow (split-window nil -10 'below)))
    (set-window-buffer goalswindow goalsbuf)
    (set-window-dedicated-p goalswindow 't)))

;; Main function creating the mode (lambdapi)
;;;###autoload
(define-derived-mode lambdapi-mode prog-mode "LambdaPi"
  "A mode for editing LambdaPi files."
  (set-syntax-table lambdapi-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-font-lock-keywords))
  (setq-default indent-tabs-mode nil) ; Indent with spaces
  (set-input-method "LambdaPi")

  ;; Comments
  (setq-local comment-start "//")
  (setq-local comment-end "")

  ;; Completion
  (lambdapi-capf-setup)

  ;; Indentation
  (smie-setup
   lambdapi--smie-prec
   'lambdapi--smie-rules
   :forward-token #'lambdapi--smie-forward-token
   :backward-token #'lambdapi--smie-backward-token)
  ;; Reindent on colon
  (electric-indent-mode -1) ; Disable electric indent by default
  (setq-local electric-indent-chars (append '(?↪ ?≔ ?:) electric-indent-chars))

  ;; Abbrev mode
  (lambdapi-abbrev-setup)

  ;; LSP
  (add-to-list
   'eglot-server-programs
   '(lambdapi-mode . ("lambdapi" "lsp" "--standard-lsp")))
  (eglot-ensure)

  ;; set column offsets for lambdapi's LSP server
  (setq-local eglot-move-to-column-function #'eglot-move-to-column)

  ;; Hooks for goals
  (add-hook 'post-command-hook #'lambdapi-update-line-number nil :local)
  ;; Hook binding line change to re-execution of proof/goals
  (add-hook 'lambdapi-changed-line-hook #'lp-display-goals)
  (lambdapi-create-goals-buffer))

;; Register mode the the ".lp" extension
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.dk\\'" . lambdapi-legacy-mode))

(provide 'lambdapi-mode)
;;; lambdapi-mode.el ends here
