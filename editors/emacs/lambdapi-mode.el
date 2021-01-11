;;; lambdapi-mode.el --- A major mode for editing Lambdapi source code -*- lexical-binding: t; -*-

;; Copyright (C) 2020 Deducteam

;; Authors: Ashish Barnawal, Diego Riviero, Gabriel Hondet, Rodolphe Lepigre 
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

(defconst lambdapi--temp-buffer-name "lp-asdf2io3jnc"  ; any random name will work
  "Buffer name for used by `lambdapi-refresh-window-layout'. Must
not match any buffer used by user")


(defun lambdapi-update-line-number ()
  (if interactive-goals
      (let ((new-line-number (line-number-at-pos)))
        (when (not (equal new-line-number lambdapi-current-line-number))
          (setq lambdapi-current-line-number new-line-number)
          (run-hooks 'changed-line-hook)))))

(defun lambdapi--apply-window-layout (tree)
  "Applies the window configuration given by the argument tree,
it is either a list (split-side ratio child1-tree child2-tree)
or a leaf which is a buffer or a string with buffer's name.

It is meant to be called by `lambdapi-refresh-window-layout'
which also replaces buffers with name `lambdapi--temp-buffer-name'
with the current buffer.

Example:

(lambdapi--apply-window-layout
               '(h 0.6 \"proofs\" (v 0.3 \"goals\" \"logs\")))

will produce

+------------+--------+
|            | goals  |
|   proofs   +--------+
|            | logs   |
|            |        |
+------------+--------+
"
  (if (not (listp tree))
      (switch-to-buffer (eval tree) t t)
    (let* ((way   (car tree))
           (ratio  (eval (cadr tree)))
           (child1 (caddr tree))
           (child2 (cadddr tree))
           curwin sibling)
      (if (eq way 'h)
          (progn
            (split-window-horizontally
             (truncate (* ratio (window-width))))
            (setq curwin  (selected-window))
            (setq sibling (next-window)))
        (progn
          (split-window-vertically
           (truncate (* ratio (window-height))))
          (setq curwin  (selected-window))
          (setq sibling (next-window))))
      (with-selected-window curwin
        (lambdapi--apply-window-layout child1))
      (with-selected-window sibling
        (lambdapi--apply-window-layout child2)))))

(defun lambdapi-refresh-window-layout ()
  "Resets the window layout to default."
  (interactive)
  (let ((curbuf (current-buffer)))
    (delete-other-windows)
    (lambdapi--apply-window-layout lambdapi-window-layout)
    (dolist (win (get-buffer-window-list lambdapi--temp-buffer-name))
      (with-selected-window win
        (switch-to-buffer curbuf t t)))
    (kill-buffer lambdapi--temp-buffer-name)
    (select-window (get-buffer-window curbuf))))

(defvar lambdapi-mode-map nil "Keymap for `lambdapi-mode'")

;; define keybindings
(progn
  (setq lambdapi-mode-map (make-sparse-keymap))
  (define-key lambdapi-mode-map (kbd "C-c C-c") #'lp-display-goals)
  (define-key lambdapi-mode-map (kbd "C-c C-i") #'toggle-interactive-goals)
  (define-key lambdapi-mode-map (kbd "C-c C-p") #'lp-proof-backward)
  (define-key lambdapi-mode-map (kbd "C-c C-n") #'lp-proof-forward)
  (define-key lambdapi-mode-map (kbd "C-c C-f") #'lp-jump-proof-forward)
  (define-key lambdapi-mode-map (kbd "C-c C-b") #'lp-jump-proof-backward)
  (define-key lambdapi-mode-map (kbd "C-c C-r") #'lambdapi-refresh-window-layout))

(defgroup lambdapi nil
  "LambdaPi is a proof assistant based on the λΠ-calculus modulo rewriting"
  :group 'languages)

(defcustom lambdapi-window-X-ratio 0.5
  "Ratio of height taken in horizontal split during window layout"
  :type '(float)
  :group 'lambdapi)

(defcustom lambdapi-window-Y-ratio 0.8
  "Ratio of width taken in vertical split during window layout"
  :type '(float)
  :group 'lambdapi)

(defcustom lambdapi-window-layout '(v lambdapi-window-Y-ratio
                                      lambdapi--temp-buffer-name
                                      (h 0.5 "*Goals*" "*lp-logs*"))
  "Window layout of LambdaPi."
  :group 'lambdapi
  ;; :set might change window layout at an unexpected time
  :set (lambda (option newval)
         (setq lambdapi-window-layout newval)
         (lambdapi-refresh-window-layout))
  :type '(radio (sexp :tag "Layout 1"
                      :format "%t\n"
                      :value
                      (v lambdapi-window-Y-ratio
                         lambdapi--temp-buffer-name
                         (h 0.5 "*Goals*" "*lp-logs*")))
                (sexp :tag "Layout 2"
                      :format "%t\n"
                      :value
                      (v lambdapi-window-Y-ratio
                         (h lambdapi-window-X-ratio
                            lambdapi--temp-buffer-name
                            "*lp-logs*")
                         "*Goals*"))
                (sexp :tag "Layout 3"
                      :format "%t\n"
                      :value
                      (h lambdapi-window-X-ratio
                         lambdapi--temp-buffer-name
                         (v lambdapi-window-Y-ratio
                            "*lp-logs*"
                            "*Goals*")))
                (sexp :tag "Layout 4"
                      :format "%t\n"
                      :value
                      (h lambdapi-window-X-ratio
                         (v lambdapi-window-Y-ratio
                            lambdapi--temp-buffer-name
                            "*Goals*")
                         "*lp-logs*"))
                (sexp :tag "Goal bottom"
                      :format "%t\n"
                      :value
                      (v lambdapi-window-Y-ratio
                         lambdapi--temp-buffer-name
                         "*Goals*"))
                (sexp :tag "Goal right"
                      :format "%t\n"
                      :value
                      (h lambdapi-window-X-ratio
                         lambdapi--temp-buffer-name
                         "*Goals*"))))


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

  ;; define keybindings
  (use-local-map lambdapi-mode-map)

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
  (lambdapi-refresh-window-layout))

;; Register mode the the ".lp" extension
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.dk\\'" . lambdapi-legacy-mode))

(provide 'lambdapi-mode)
;;; lambdapi-mode.el ends here
