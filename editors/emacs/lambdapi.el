;;; This is the LambdaPi emacs mode
(provide 'lambdapi-mode)
(provide 'lambdapi-legacy-mode)

;; Syntax table
(defvar lambdapi-mode-syntax-table nil "Syntax table for LambdaPi.")

(setq lambdapi-mode-syntax-table
  (let ((synTable (make-syntax-table)))
    (modify-syntax-entry ?\/ ". 12b" synTable)
    (modify-syntax-entry ?\n "> b" synTable)
    synTable))

;; Keywords
(defconst lambdapi-font-lock-keywords
  (list (cons (concat "\\<" (regexp-opt '(
    "require" "open" "as" "let" "in" "symbol" "const" "injective" "rule" "and"
    "definition" "theorem" "assert" "assertnot" "set" "proof" "qed" "admit"
    "abort" "focus" "print" "proofterm" "refine" "apply" "simpl" "intro"
    "rewrite" "reflexivity" "symmetry" "type" "compute"
  )) "\\>") 'font-lock-keyword-face))
  "Keyword highlighting for the LambdaPi mode.")

;; Unicode support
(require 'quail)
(quail-define-package
  "LambdaPi" "LambdaPi" "LambdaPi" t
  "A transliteration scheme for LambdaPi."
  nil t t t t nil t nil nil nil t)
(quail-define-rules
  ("->"   ?→) ("\\to" ?→) ("\\rightarrow" ?→)
  ("=>"   ?⇒) ("\\To" ?⇒) ("\\Rightarrow" ?⇒)
  ("!"    ?∀) ("\\forall" ?∀)
  ("\\"   ?λ) ("\\lambda" ?λ)
  (":="   ?≔) ("\\defeq"  ?≔)
  ("=="   ?≡) ("\\equiv"  ?≡))

;; Main function creating the mode (lambdapi)
(define-derived-mode lambdapi-mode fundamental-mode "LambdaPi"
  "A mode for editing LambdaPi files."
  (set-syntax-table lambdapi-mode-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-font-lock-keywords))
  (setq-local comment-start "//")
  (setq-local comment-end "")
  (setq-default indent-tabs-mode nil)
  (set-input-method "LambdaPi"))

;; Syntax table (legacy syntax)
(defvar lambdapi-mode-legacy-syntax-table nil "Syntax table for LambdaPi.")

(setq lambdapi-mode-legacy-syntax-table
  (let ((synTable (make-syntax-table)))
    (modify-syntax-entry ?\( ". 1" synTable)
    (modify-syntax-entry ?\) ". 4" synTable)
    (modify-syntax-entry ?\; ". 23" synTable)
    synTable))

;; Keywords (legacy syntax)
(defconst lambdapi-legacy-font-lock-keywords
  (list (cons (concat "\\<" (regexp-opt '(
           "def" "thm" "inj"
        )) "\\>") 'font-lock-keyword-face)
        (cons (concat "#" (regexp-opt '(
           "REQUIRE" "EVAL" "INFER" "ASSERT" "ASSERTNOT"
        )) "\\>") 'font-lock-preprocessor-face))
  "Keyword highlighting for the LambdaPi mode (legacy syntax).")


;; Main function creating the mode (legacy syntax)
(define-derived-mode lambdapi-legacy-mode fundamental-mode "LambdaPi (legacy)"
  "A mode for editing LambdaPi files (in legacy syntax)."
  (set-syntax-table lambdapi-mode-legacy-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-legacy-font-lock-keywords))
  (setq-local comment-start "(;")
  (setq-local comment-end ";)")
  (setq-default indent-tabs-mode nil))

;; LSP mode
(require 'eglot)
(add-to-list 'eglot-server-programs
  '(lambdapi-mode . ("lp-lsp" "--std")))
(add-to-list 'eglot-server-programs
  '(lambdapi-legacy-mode . ("lp-lsp" "--std")))
(add-hook 'lambdapi-mode-hook 'eglot-ensure)
(add-hook 'lambdapi-legacy-mode-hook 'eglot-ensure)

;; Register mode the the ".lp" extension
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))
(add-to-list 'auto-mode-alist '("\\.dk\\'" . lambdapi-legacy-mode))

;;; lambdapi.el ends here
