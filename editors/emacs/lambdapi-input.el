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

(defun lambdapi--add-translation (tbl tags)
  "Add translation from list TBL whose tag is in TAGS."
  (cl-map
   nil
   (lambda (sym)
     (when (cl-member (car sym) tags :test 'string=)
       (quail-defrule (cadr sym) (cddr sym))))
   tbl))

;; Add greek letters and binary operators from `math-symbol-list-basic'
(lambdapi--add-translation math-symbol-list-basic
                           '("greek" "Greek" "bin" "rel" "misc"))

(provide 'lambdapi-input)
;;; lambdapi-input.el ends here
