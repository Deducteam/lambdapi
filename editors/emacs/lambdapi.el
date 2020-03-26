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

(defconst dk3-ident "[a-zA-Z_][a-zA-Z0-9_]*")
(defconst dk3-nat-lit "[0-9]+")
(defconst dk3-float-lit "[0-9]+\\([.][0-9]+\\)?")
(defconst lp-keywords--tactics
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

(defconst lp-keywords--proof-finish
  '("admit" "qed" "abort"))

(defconst lp-keywords--terms
  '("in" "let" "λ" "∀" "," "TYPE" "→" "⇒" "≔"))

(defconst lp-keywords--misc-commands
  '("assert" "assertnot" "type" "compute"))

(defconst lp-keywords--commands
  '("and" "symbol" "theorem" "definition" "rule" "proof" ":"))

(defconst lp-keywords--symtags
  '("protected" "injective" "constant" "private"))

(defconst lp-keywords--modules
  '("require" "import" "as" "open" "."))

(defconst lp-keywords--params
  '("set" "verbose" "prover" "prover_timeout" "prefix" "infix" "left" "right"))

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

(defconst lp-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((ident ("ID"))
      (qident (ident "." ident))
      (rw-patt)
      (args (ident)
            (ident ":" sterm))
      (sterm ("TYPE")
             ("_")
             (ident)
             (sterm "⇒" sterm)
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
               ("theorem" args ":" sterm "proof" tactic "PRFEND")
               ("definition" args "≔" sterm)
               ("rule" rules)
               ("assert" sterm "≡" sterm)
               ("compute" sterm)
               ("type" sterm ":" sterm)
               ("require" qident)
               ("require" qident "as" ident)
               ("require" "open" qident)
               ("set" "verbose" "NATLIT")
               ("set" "debug" ident)
               ("set" "builtin" ident "≔" qident)
               ("set" "prefix" "FLOATLIT" "\"" ident "\"" "≔" qident)
               ("set" "infix" "FLOATLIT" ident "≔" qident)
               ("set" "infix" "left" "FLOATLIT" ident "≔" qident)
               ("set" "infix" "right" "FLOATLIT" ident "≔" qident)
               ("set" "prover" ident)
               ("set" "prover_timeout" "NATLIT")
               ("set" "declared" ident)))
    '((assoc ":" "theorem"))
    '((assoc ":" "symbol"))
    '((assoc ",") (assoc "in") (right "⇒")))))

(defconst dk3-keywords--main-regexp
  (regexp-opt
   (append
    lp-keywords--tactics
    lp-keywords--params
    lp-keywords--terms
    lp-keywords--modules
    lp-keywords--commands
    lp-keywords--symtags
    lp-keywords--misc-commands)))

;; TODO: literals with double quotes for set infix etc
(defun dedukti-smie-forward-token ()
  "Forward lexer for Dedukti3."
  ;; Skip comments
  (forward-comment (point-max))
  (cond
   ;; qed, admit or abort as "PRFEND"
   ((looking-at (regexp-opt lp-keywords--proof-finish))
    (goto-char (match-end 0))
    "PRFEND")
   ((looking-at dk3-keywords--main-regexp)
    (goto-char (match-end 0))
    (match-string-no-properties 0))
   ;; nat lit
   ((looking-at dk3-nat-lit)
    (goto-char (match-end 0))
    "NATLIT")
   ;; float lit
   ((looking-at dk3-float-lit)
    (goto-char (match-end 0))
    "FLOATLIT")
   ;; identifiers
   ((looking-at dk3-ident)
    (goto-char (match-end 0))
    "ID")
   ;; TODO: Case to distinguish top ":" from arguments ":"
   (t (buffer-substring-no-properties
       (point)
       (progn (skip-syntax-forward "w_")
              (point))))))

(defun dedukti-smie-backward-token ()
  "Backward lexer for Dedukti3."
  (forward-comment (- (point)))
  (cond
   ((looking-back dk3-keywords--main-regexp (- (point) 13) t)
    (goto-char (match-beginning 0))
    (match-string-no-properties 0))
   ;; naturals
   ((looking-back dk3-nat-lit nil t)
    (goto-char (match-beginning 0))
    "NATLIT")
   ;; floats
   ((looking-back dk3-float-lit nil t)
    (goto-char (match-beginning 0))
    "FLOATLIT")
   ;; identifiers
   ((looking-back dk3-ident nil t)
    (goto-char (match-beginning 0))
    "ID")
   ;; TODO: same, case for ":"
   (t (buffer-substring-no-properties
       (point)
       (progn (skip-syntax-backward "w_")
              (point))))))
(defun dedukti-backward ()
  "Move backward by one token or by a sexp."
  (interactive)
  (let ((beg (point)))
    (prog1
        (or (dedukti-smie-backward-token)
            (backward-sexp))
      (when (eq beg (point))
        (backward-char)))))

(defun dedukti-smie-backward-debug ()
  "Print the current value of `dedukti-smie-backward-token'."
  (interactive)
  (let ((v (dedukti-backward)))
    (when v (princ v))))

(defun lp-smie-rules (kind token)
  "Indentation rule for case KIND and token TOKEN."
  (pcase (cons kind token)
    (`(:elem . basic) 0)
    ;; Toplevel
    (`(:before . "symbol") '(column 0))
    (`(:before . "theorem") '(column 0))
    (`(:before . "type") '(column 0))
    (`(:before . "set") '(column 0))))

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
