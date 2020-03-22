;;; lambdapi-mode --- A major mode to edit Dedukti files

;; Author: Rodolphe Lepigre, Gabriel Hondet
;; Keywords: lambdapi dedukti proof-assistant
;; Compatibility: GNU Emacs 26.1
;; Package-Requires: ((quail))

;;; Commentary:

;;; Code:

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

(defconst lp-keywords--proofs
  '("abort"
    "admit"
    "apply"
    "assume"
    "focus"
    "print"
    "proofterm"
    "qed"
    "refine"
    "reflexivity"
    "rewrite"
    "simpl"
    "symmetry"
    "why3"))

(defconst lp-keywords--terms
  '("in" "let" "λ" "∀" "TYPE"))

(defconst lp-keywords--misc-commands
  '("assert" "assertnot" "type" "compute"))

(defconst lp-keywords--commands
  '("and" "symbol" "theorem" "definition" "rule" "proof" "admit" "qed" "abort"))

(defconst lp-keywords--symtags
  '("protected" "injective" "constant" "private"))

(defconst lp-keywords--modules
  '("require" "import" "as" "open"))

;; Keywords
(defconst lambdapi-font-lock-keywords
  (list (cons
         (concat "\\<" (regexp-opt (append lp-keywords--commands
                                           lp-keywords--symtags
                                           lp-keywords--modules)) "\\>")
         'font-lock-keyword-face)
        (cons
         (concat "\\<" (regexp-opt lp-keywords--misc-commands) "\\>")
         'font-lock-preprocessor-face))
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

;; SMIE indentation engine
(require 'smie)

;; TODO: forward and backward token

(defconst lp-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((ident)
      (qident (ident))
      (rw-patt)
      (nat-lit)
      (args (ident)
            (ident ":" sterm))
      (sterm ("TYPE")
             ("_")
             (sterm "⇒" sterm)
             (ident)
             ("λ" args "," sterm)
             ("∀" args "," sterm)
             ("let" args "≔" sterm "in" sterm))
      (tactic ("refine" sterm)
              ("assume" sterm)
              ("apply" sterm)
              ("simpl")
              ("rewrite" "[" rw-patt "]" sterm)
              ("reflexivity")
              ("focus" nat-lit)
              ("print")
              ("proofterm")
              ("why3"))
      (rule (sterm "→" sterm))
      (rules (rule)
             (rule "and" rule))
      (symtag ("constant" "injective" "protected" "private"))
      (command (symtag "symbol" args ":" sterm)
               ("theorem" args ":" sterm "proof" tactic "qed")
               ("theorem" args ":" sterm "proof" tactic "admit")
               ("theorem" args ":" sterm "proof" tactic "abort")
               ("definition" args "≔" sterm)
               ("rule" rules)
               ("assert" sterm "≡" sterm)
               ("compute" sterm)
               ("type" sterm ":" sterm)
               ("require" qident)
               ("require" qident "as" ident)
               ("require" "open" qident)
               ("set" "verbose" nat-lit)
               ("set" "debug" ident)
               ("set" "builtin" ident "≔" qident)
               ("set" "prefix" ident "≔" qident)
               ("set" "infix" ident "≔" qident)
               ("set" "infix" "left" ident "≔" qident)
               ("set" "infix" "right" ident "≔" qident)
               ("set" "prover" ident)
               ("set" "prover_timeout" nat-lit)
               ("set" "declared" ident)))
    '((assoc ":" "theorem"))
    '((assoc ":" "symbol"))
    '((assoc ",") (assoc "in") (right "⇒")))))

(defun lp-smie-rules (kind token)
  "Indentation rule for case KIND and token TOKEN."
  (let ((command (or "symbol" "theorem" "assert" "compute" "type" "rule"
                     "definition" "set" "require" "assertnot")))
    (pcase (cons kind token)
      ;; (`(:before . basic)
      ;;  ,(if (and (smie-rule-parent-p '("require")) (smie-rule-bolp)))
      ;;  (cons 'column 2))
      (`(:after . basic)
       ,(if (and (smie-rule-parent-p '("as")) (smie-rule-hanging-p)) '('column 0)))
      (`(:before . command) '('column 0)))))

;; Main function creating the mode (lambdapi)
;;;###autoload
(define-derived-mode lambdapi-mode prog-mode "LambdaPi"
  "A mode for editing LambdaPi files."
  (set-syntax-table lambdapi-mode-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-font-lock-keywords))
  (setq-local comment-start "//")
  (setq-local comment-end "")
  (smie-setup lp-smie-grammar #'lp-smie-rules)
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
