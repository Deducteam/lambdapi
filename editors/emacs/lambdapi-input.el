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

(require 'seq)
(defconst lambdapi--math-symbol-list-basic
  (eval-when-compile
    (let* ((cat-rx (rx (or "arrow" "greek" "Greek" "bin" "rel" "misc")))
           (pred (lambda (sym) (string-match-p cat-rx (car sym))))
           (filt (seq-filter pred math-symbol-list-basic)))
      (seq-map (lambda (sym) `(,(cadr sym) . ,(cddr sym))) filt)))
  "Formatted sublist of `math-symbol-list-basic'.
An element of this list is a dotted pair (COM . CH) where com is the LaTeX
command (e.g. \alpha) and CH is the character (e.g. α).")

(defconst lambdapi--math-symbol-list-extended
  (eval-when-compile
    (let* ((com-rx "\\Bbb.")
           (pred (lambda (sym) (string-match-p com-rx (cadr sym))))
           (filt (seq-filter pred math-symbol-list-extended)))
      (seq-map (lambda (sym) `(,(cadr sym) . ,(cdddr sym))) filt)))
  "Formatted sublist of `math-symbol-list-extended'.
An element of this list is a dotted pair (COM . CH) where com is the LaTeX
command (e.g. \alpha) and CH is the character (e.g. α).")

(when (or lambdapi-unicode-force-quail (not (require 'company-math nil 1)))
  (seq-do (lambda (com-ltx) (quail-defrule (car com-ltx) (cdr com-ltx)))
          (seq-concatenate 'list
                           lambdapi--math-symbol-list-basic
                           lambdapi--math-symbol-list-extended)))

(provide 'lambdapi-input)
;;; lambdapi-input.el ends here
