;;; lambdapi-input.el --- Input method for lambdapi -*- lexical-binding: t; -*-
;;
;; Package-Requires: ((emacs 26.1) (cl-lib "0.5") (math-symbol-lists "1.2.1"))
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;;  Input method for lambdapi. Define a quail package with symbols from
;;  `math-symbol-lists'.
;;  The input method is augmented with more latex symbols if company is not
;;  available because if the input method is active (that is, a sequence of
;;  characters is candidate to be translated), compnay won't show suggestions.
;;
;;; Code:
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

(defun lambdapi--add-translation (tbl tags)
  "Add translation from list TBL whose tag is in TAGS."
  (cl-map
   nil
   (lambda (sym)
     (when (cl-member (car sym) tags :test 'string=)
       (quail-defrule (cadr sym) (cddr sym))))
   tbl))

;; Add greek letters and binary operators from `math-symbol-list-basic'
(unless (and (require 'company nil 1) (require 'company-math nil 1))
  (lambdapi--add-translation
   math-symbol-list-basic '("greek" "Greek" "bin" "rel" "misc")))

(provide 'lambdapi-input)
;;; lambdapi-input.el ends here
