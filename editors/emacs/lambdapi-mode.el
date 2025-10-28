;;; lambdapi-mode.el --- A major mode for editing Lambdapi source code -*- lexical-binding: t; -*-

;; Copyright (C) 2020-2024 Deducteam

;; Authors: Ashish Barnawal, Diego Riviero, Gabriel Hondet, Rodolphe Lepigre
;; Maintainer: Deducteam <dedukti-dev@inria.fr>
;; Version: 1.1.0
;; SPDX-License-Identifier: CECILL-2.1
;; Homepage: https://github.com/Deducteam/lambdapi
;; Keywords: languages
;; Compatibility: GNU Emacs 27.1
;; Package-Requires: ((emacs "27.1") (eglot "1.6") (math-symbol-lists "1.2.1") (highlight "20190710.1527"))

;;; Commentary:

;;  A major mode for editing Lambdapi source code. This major mode provides
;;  indentation, syntax highlighting, completion, easy unicode input, and more.

;;; Code:

(require 'eglot)
(require 'lambdapi-abbrev)
(require 'lambdapi-capf)
(require 'lambdapi-input)
(require 'lambdapi-layout)
(require 'lambdapi-proofs)
(require 'lambdapi-smie)
(require 'lambdapi-vars)

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
     "\\>")
    'font-lock-keyword-face)
   (cons
    (concat
     "#"
     (regexp-opt '("REQUIRE" "EVAL" "INFER" "ASSERT" "ASSERTNOT"))
     "\\>")
    'font-lock-preprocessor-face))
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
  (if electric-terminator
      (let ((new-line-number (line-number-at-pos)))
        (when (not (equal new-line-number lambdapi-current-line-number))
          (setq lambdapi-current-line-number new-line-number)
          (run-hooks 'changed-line-hook)))))

(defvar lambdapi-mode-map nil "Keymap for `lambdapi-mode'")

(defun lambdapi-eglot-reconnect ()
  (interactive)
  (let ((current-server (eglot-current-server)))
    (call-interactively
     (if (and current-server (jsonrpc-running-p current-server))
         #'eglot-reconnect #'eglot))))

;; define keybindings
(progn
  (setq lambdapi-mode-map (make-sparse-keymap))
  (define-key lambdapi-mode-map (kbd "C-c C-c") #'lp-prove-till-cursor)
  (define-key lambdapi-mode-map (kbd "C-c C-e") #'lp-toggle-electric-terminator)
  (define-key lambdapi-mode-map (kbd "C-c C-p") #'lp-proof-backward)
  (define-key lambdapi-mode-map (kbd "C-c C-n") #'lp-proof-forward)
  (define-key lambdapi-mode-map (kbd "C-c C-f") #'lp-jump-proof-forward)
  (define-key lambdapi-mode-map (kbd "C-c C-b") #'lp-jump-proof-backward)
  (define-key lambdapi-mode-map (kbd "C-c C-r") #'lambdapi-eglot-reconnect)
  (define-key lambdapi-mode-map (kbd "C-c C-k") #'eglot-shutdown)
  ;; define toolbar
  (define-key lambdapi-mode-map [tool-bar lp-toggle-electric-terminator]
    '(menu-item "" lp-toggle-electric-terminator
                :image (image :type xpm :file "disconnect.xpm")
                :help "Toggle electric terminator"))
  (define-key lambdapi-mode-map [tool-bar lp-prove-till-cursor]
    '(menu-item "" lp-prove-till-cursor
                :image (image :type xpm :file "jump-to.xpm")
                :help "Prove till cursor"))
  (define-key lambdapi-mode-map [tool-bar lp-proof-jump-forward]
    '(menu-item "" lp-jump-proof-forward
                :image (image :type xpm :file "next-node.xpm")
                :help "Next Proof"))
  (define-key lambdapi-mode-map [tool-bar lp-proof-jump-backward]
    '(menu-item "" lp-jump-proof-backward
                :image (image :type xpm :file "prev-node.xpm")
                :help "Previous Proof"))
  (define-key lambdapi-mode-map [tool-bar lp-proof-forward]
    '(menu-item "" lp-proof-forward
                :image (image :type xpm :file "right-arrow.xpm")
                :help "Go Forward"))
  (define-key lambdapi-mode-map [tool-bar lp-proof-backward]
    '(menu-item "" lp-proof-backward
                :image (image :type xpm :file "left-arrow.xpm")
                :help "Go backward")))

(defgroup lambdapi nil
  "LambdaPi is a proof assistant based on the λΠ-calculus modulo rewriting"
  :group 'languages)

(defun pre-process-diagnostics  (orig-fun server method uri diagnostics de e)
  
  (apply orig-fun (list server method uri diagnostics de e))
)

;; Main function creating the mode (lambdapi)
;;;###autoload
(define-derived-mode lambdapi-mode prog-mode "LambdaPi"
  "A mode for editing LambdaPi files."
  (set-syntax-table lambdapi-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-font-lock-keywords))
  (setq-default indent-tabs-mode nil) ; Indent with spaces
  (set-input-method "LambdaPi")

  ;;pre-process diagnostics
  (advice-add 'eglot-handle-notification :around #'pre-process-diagnostics)
  (message "Eglot-X: diagnostic filtering enabled.")

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

  ;; ensure diagnostics don't hide hover results
  (add-to-list 'eglot-stay-out-of 'eldoc-documentation-strategy)
  (setq-local eldoc-documentation-strategy #'eldoc-documentation-compose)

  ;; LSP
  (add-to-list
   'eglot-server-programs
   '(lambdapi-mode . ("lambdapi" "lsp" "--standard-lsp")))
  (eglot-ensure)

  ;; Hooks for goals
  (add-hook 'post-command-hook #'lambdapi-update-line-number nil :local)
  ;; Hook binding line change to re-execution of proof/goals
  (add-hook 'lambdapi-changed-line-hook #'lp-display-goals)
  (add-hook 'post-self-insert-hook 'lp--post-self-insert-function 100 t)
  (add-hook 'after-change-functions 'lp--after-change-function 100 t)

  (lambdapi-refresh-window-layout))

;; Register mode the the ".lp" extension
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.dk\\'" . lambdapi-legacy-mode))

(provide 'lambdapi-mode)
;;; lambdapi-mode.el ends here
