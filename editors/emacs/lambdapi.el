;;; lambdapi-mode --- A major mode to edit Dedukti files -*- lexical-binding: t; -*-

;; Author: Rodolphe Lepigre, Gabriel Hondet
;; Keywords: lambdapi dedukti proof-assistant
;; Compatibility: GNU Emacs 26.1
;; Package-Requires: ((emacs "26.1") (quail))

;;; Commentary:
;;
;;; Code:

(require 'lambdapi-smie)
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
  (setq-default indent-tabs-mode nil))

;;; Dedukti3
;; Syntax table
(defvar lambdapi-mode-syntax-table nil "Syntax table for LambdaPi.")

(setq lambdapi-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\/ ". 12b" st)
    (modify-syntax-entry ?\n "> b" st)
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?& "_" st)
    st))

;; Keywords
(defconst lambdapi-font-lock-keywords
  (list (cons
         (concat "\\<"
                 (regexp-opt
                  '("theorem"
                    "proof"
                    "admit"
                    "abort"
                    "qed"
                    "symbol"
                    "rule"
                    "and"))
                 "\\>")
         'font-lock-keyword-face)
        (cons
         (concat "\\<"
                 (regexp-opt
                  '("set"
                    "require"
                    "open"
                    "as"
                    "type"
                    "assert"
                    "assertnot"
                    "compute"))
                 "\\>")
         'font-lock-preprocessor-face)
        (cons
         (concat "\\<"
                 (regexp-opt
                  '("refine"
                    "assume"
                    "apply"
                    "proofterm"
                    "rewrite"
                    "print"))
                 "\\>")
         'font-lock-builtin-face)
        (cons
         (concat "\\<"
                 (regexp-opt '("TYPE" "left" "right" "infix" "prefix"))
                 "\\>")
         'font-lock-constant-face))
  "Keyword highlighting for the LambdaPi mode.")

;; Unicode support
(require 'quail)
(quail-define-package
  "LambdaPi" "LambdaPi" "LambdaPi" t
  "A transliteration scheme for LambdaPi."
  nil t t t t nil t nil nil nil t)
(quail-define-rules
  ("->" ?→) ("\\to" ?→) ("\\rightarrow" ?→)
  ("=>" ?⇒) ("\\To" ?⇒) ("\\Rightarrow" ?⇒)
  ("!!" ?∀) ("\\forall" ?∀)
  ("\\\\" ?λ) ("\\lambda" ?λ)
  (":=" ?≔) ("\\defeq"  ?≔)
  ("==" ?≡) ("\\equiv"  ?≡)
  ("&&" ?∧) ("\\wedge"  ?∧) ("/\\" ?∧)
  ("||" ?∨) ("\\vee"    ?∨) ("\\/" ?∨)
  ("~~" ?¬) ("\\neg"    ?¬)
  ("??" ?∃) ("\\exists" ?∃)
  ("`a" ?α) ("`b" ?β) ("`c" ?γ) ("`d" ?δ)
  ("`e" ?ε) ("`h" ?η) ("`i" ?ι) ("`k" ?κ)
  ("`m" ?μ) ("`n" ?ν) ("`o" ?ω) ("`p" ?π)
  ("`r" ?ρ) ("`s" ?σ) ("`t" ?τ) ("`u" ?υ)
  ("`w" ?ω) ("`x" ?χ) ("`y" ?υ) ("`z" ?ζ)
  ("`C" ?Γ) ("`D" ?Δ) ("`G" ?Γ) ("`L" ?Λ)
  ("`O" ?Ω) ("`P" ?Π) ("`S" ?Σ) ("`W" ?Ω))

;; Main function creating the mode (lambdapi)
;;;###autoload
(define-derived-mode lambdapi-mode prog-mode "LambdaPi"
  "A mode for editing LambdaPi files."
  (set-syntax-table lambdapi-mode-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-font-lock-keywords))
  (setq-local comment-start "//")
  (setq-local comment-end "")
  (smie-setup
   lp-smie-grammar
   #'lp-smie-rules
   :forward-token #'dedukti-smie-forward-token
   :backward-token #'dedukti-smie-backward-token)
  (setq-default indent-tabs-mode nil)
  (set-input-method "LambdaPi"))

;; LSP mode
(if (not (version<= emacs-version "26"))
    (progn
      (require 'eglot)
      (add-to-list 'eglot-server-programs
                   '(lambdapi-mode . ("lambdapi" "lsp" "--standard-lsp")))
      (add-to-list 'eglot-server-programs
                   '(lambdapi-legacy-mode . ("lambdapi" "lsp" "--standard-lsp")))
      (add-hook 'lambdapi-mode-hook 'eglot-ensure)
      (add-hook 'lambdapi-legacy-mode-hook 'eglot-ensure)))

;; Register mode the the ".lp" extension
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("\\.dk\\'" . lambdapi-legacy-mode))

(provide 'lambdapi-mode)
(provide 'lambdapi-legacy-mode)
;;; lambdapi.el ends here
