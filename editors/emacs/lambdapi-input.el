;;; lambdapi-input.el --- Input method for lambdapi -*- lexical-binding: t; -*-
;;; Commentary:
;;
;;  Input method for lambdapi. Define a quail package with symbols from
;;  `math-symbol-lists'.
;;  The input method is augmented with more latex symbols if company is not
;;  available because if the input method is active (that is, a sequence of
;;  characters is candidate to be translated), compnay won't show suggestions.
;;
;;; Code:
(require 'lambdapi-vars)
(require 'cl-lib)
(require 'quail)
(require 'math-symbol-lists)

(quail-define-package
  "LambdaPi" "LambdaPi" "LambdaPi" t
  "A transliteration scheme for LambdaPi."
  nil t t t t nil t nil nil nil t)
(quail-define-rules
  ("->" ?→) ("=>" ?⇒) ("!!" ?∀) ("\\\\" ?λ)
  (":=" ?≔) ("==" ?≡)
  ("&&" ?∧) ("/\\" ?∧)
  ("||" ?∨) ("\\/" ?∨)
  ("~~" ?¬) ("??" ?∃)
  ("`a" ?α) ("`b" ?β) ("`c" ?γ) ("`d" ?δ)
  ("`e" ?ε) ("`h" ?η) ("`i" ?ι) ("`k" ?κ)
  ("`m" ?μ) ("`n" ?ν) ("`o" ?ω) ("`p" ?π)
  ("`r" ?ρ) ("`s" ?σ) ("`t" ?τ) ("`u" ?υ)
  ("`w" ?ω) ("`x" ?χ) ("`y" ?υ) ("`z" ?ζ)
  ("`C" ?Γ) ("`D" ?Δ) ("`G" ?Γ) ("`L" ?Λ)
  ("`O" ?Ω) ("`P" ?Π) ("`S" ?Σ) ("`W" ?Ω))

;; If loading time becomes too long because loading lists too big, sublists can
;; be computed at compile time with (eval-when-compile) which can then be loaded

(defun lambdapi--add-translation (tbl tags)
  "Add translation from list TBL whose tag is in TAGS."
  (cl-map
   nil
   (lambda (sym)
     (when (cl-member (car sym) tags :test 'string=)
       (quail-defrule (cadr sym) (cddr sym))))
   tbl))

(defun lambdapi--add-ext-translation (tbl com-rx)
  "Add translation from list TBL whose command matches COM-RX."
  (cl-map
   nil
   (lambda (sym)
     (when (string-match-p com-rx (cadr sym))
       (quail-defrule (cadr sym) (cdddr sym))))
   tbl))

;; Add greek letters and binary operators from `math-symbol-list-basic'
;; Use quail when can't use company-math or quail is forced
(when (or lambdapi-unicode-force-quail (not (require 'company-math nil 1)))
  (lambdapi--add-translation
   math-symbol-list-basic '("greek" "Greek" "bin" "rel" "misc"))
  ;; Add blackboard bold
  (lambdapi--add-ext-translation math-symbol-list-extended "\\Bbb."))
(provide 'lambdapi-input)
;;; lambdapi-input.el ends here
