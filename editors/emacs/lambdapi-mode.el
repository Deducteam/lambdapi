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

(defun lambdapi-update-line-number ()
  (if interactive-goals
      (let ((new-line-number (line-number-at-pos)))
        (when (not (equal new-line-number lambdapi-current-line-number))
          (setq lambdapi-current-line-number new-line-number)
          (run-hooks 'changed-line-hook)))))


(defgroup lambdapi nil
  "LambdaPi is a proof assistant based on the λΠ-calculus modulo rewriting"
  :group 'languages)

(defcustom lambdapi-goals-window-side 'bottom
  "Side at which to show goals window"
  :type '(choice (const :tag "right"  right)
                 (const :tag "left"   left)
                 (const :tag "top"    top)
                 (const :tag "bottom" bottom))
  :group 'lambdapi)

(defcustom lambdapi-goals-window-height-ratio 0.30
  "Ratio of height taken by Goals window if split top or bottom"
  :type '(float)
  :group 'lambdapi)

(defcustom lambdapi-goals-window-width-ratio 0.5
  "Ratio of width taken by Goals window if split left or right"
  :type '(float)
  :group 'lambdapi)

(defcustom lambdapi-goals-window-min-width 40
  "Minimum width of Goals window"
  :type '(integer)
  :group 'lambdapi)

(defcustom lambdapi-goals-window-min-height 4
  "Minimum height of Goals window"
  :type '(integer)
  :group 'lambdapi)


(defun lambdapi-refresh-window-layout ()
  "Create *Goals* buffer if it is not present. Create a side window
for the goals buffer using the lambdapi-goals-window-* variables."
  (interactive)
  (let* ((goalsbuf (get-buffer-create "*Goals*"))
	 (goalswindow (get-buffer-window goalsbuf))
	 (gwin-height (truncate
		       (* lambdapi-goals-window-height-ratio
			  (frame-height))))
	 (gwin-width (truncate
		      (* lambdapi-goals-window-width-ratio
			 (frame-width)))))
    ;; Allocate window for *Goals* buffer
    (if goalswindow
	(delete-window goalswindow))
    (setq goalswindow
	  (display-buffer-in-side-window
	   goalsbuf
	   `((side . ,lambdapi-goals-window-side)
	     (slot . nil)
	     ,(pcase lambdapi-goals-window-side
		((or 'right 'left)
		 `(window-width . ,gwin-width))
		((or 'top 'bottom)
		 `(window-height . ,gwin-height))))))
    ;; if goals window violated lambdapi-goals-window-min-*
    ;; allocate a new window
    (if (and goalswindow
	     (< (window-width goalswindow)
		lambdapi-goals-window-min-width))
	(progn
	  (delete-window goalswindow)
	  (setq goalswindow
		(display-buffer-in-side-window
		 goalsbuf `((side . bottom)
			    (slot . nil)
			    (window-height . ,gwin-height))))))
    (if (and goalswindow
	     (< (window-height goalswindow)
		lambdapi-goals-window-min-height))
	(progn
	  (delete-window goalswindow)
	  (setq goalswindow
		(display-buffer-in-side-window
		 goalsbuf `((side . right)
			    (slot . nil)
			    (window-width . ,gwin-width))))))))


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
