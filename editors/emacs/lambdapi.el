;;; This is the LambdaPi emacs mode
(provide 'lambdapi-mode)

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
    "rewrite" "reflexivity" "symmetry"
  )) "\\>") 'font-lock-keyword-face))
  "Keyword highlighting for the LambdaPi mode.")

;; Unicode support
(require 'quail)
(quail-define-package
  "LambdaPi" "LambdaPi" "LambdaPi" t
  "A transliteration scheme for LambdaPi."
  nil t t t t nil t nil nil nil t)
(quail-define-rules
  ("->"   ?→) ("\\to" ?→)
  ("=>"   ?⇒) ("\\To" ?⇒)
  ("!"    ?∀) ("\\forall" ?∀)
  ("\\\\" ?λ) ("\\lambda" ?λ)
  (":="   ?≔) ("\\defeq"  ?≔))

;; Main function creating the mode
(define-derived-mode lambdapi-mode fundamental-mode "LambdaPi"
  "A mode for editing LambdaPi files."
  (set-syntax-table lambdapi-mode-syntax-table)
  (setq-local font-lock-defaults '(lambdapi-font-lock-keywords))
  (setq-local comment-start "//")
  (setq-local comment-end "")
  (setq-default indent-tabs-mode nil)
  (set-input-method "LambdaPi"))

;; LSP mode
(require 'eglot)
(add-to-list 'eglot-server-programs '(lambdapi-mode . ("lp-lsp" "--std")))
(add-hook 'lambdapi-mode-hook 'eglot-ensure)

;; Register mode the the ".lp" extension
(add-to-list 'auto-mode-alist '("\\.lp\\'" . lambdapi-mode))

;;; lambdapi.el ends here
