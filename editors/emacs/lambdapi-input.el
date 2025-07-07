;;; lambdapi-input.el --- Input method for lambdapi -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CECILL-2.1
;;; Commentary:
;;
;;  Input method for lambdapi. Define a quail package with symbols from
;;  package `math-symbol-lists'.
;;  Since Company's dropdown menu is disabled as long as there are quail
;;  candidates, some users may prefer to inhibit quail and use directly company
;;  setting `lambdapi-unicode-prefer-company' to non-nil.
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

 ;; Lambdapi syntax

 ("->" ?→) ("-->" ?↪) ("\\\\" ?λ)
 ("\\defeq" ?≔) (":=" ?≔) ("==" ?≡) ("|-" ?⊢)
 
 ;; Logical connectors

 ("\\neg" ?¬) ("~~" ?¬)
 ("\\and" ?∧) ("&&" ?∧) ("/\\" ?∧)
 ("\\or" ?∨) ("||" ?∨) ("\\/" ?∨)
 ("=>" ?⇒)
 ("<=>" ?⇔)
 ("!!" ?∀)
 ("??" ?∃)

 ;; Miscellaneous

 ("\\Box" ?□)
 ("::" ?⸬)
 ("<=" ?≤) (">=" ?≥) ("<>" ?≠)
 ("--" ?—)

 ;; Greek letters

 ("`a" ?α) ("`b" ?β) ("`g" ?γ) ("`G" ?Γ)
 ("`d" ?δ) ("`D" ?Δ) ("`e" ?ε) ("`z" ?ζ)
 ("`h" ?η) ("`i" ?ι) ("`k" ?κ) ("`l" ?λ)
 ("`L" ?Λ) ("`m" ?μ) ("`n" ?ν) ("`p" ?π)
 ("`P" ?Π) ("`r" ?ρ) ("`s" ?σ) ("`S" ?Σ)
 ("`t" ?τ) ("`u" ?υ) ("`U" ?ϒ) ("`x" ?χ)
 ("`w" ?ω) ("`W" ?Ω)

 ;; Double-struck letters

 ("`dA" ?𝔸)
 ("`dB" ?𝔹)
 ("`dC" ?ℂ)
 ("`dD" ?𝔻)
 ("`dE" ?𝔼)
 ("`dF" ?𝔽)
 ("`dG" ?𝔾)
 ("`dH" ?ℍ)
 ("`dI" ?𝕀)
 ("`dJ" ?𝕁)
 ("`dK" ?𝕂)
 ("`dL" ?𝕃)
 ("`dM" ?𝕄)
 ("`dN" ?ℕ)
 ("`dO" ?𝕆)
 ("`dP" ?ℙ)
 ("`dQ" ?ℚ)
 ("`dR" ?ℝ)
 ("`dS" ?𝕊)
 ("`dT" ?𝕋)
 ("`dU" ?𝕌)
 ("`dV" ?𝕍)
 ("`dW" ?𝕎)
 ("`dX" ?𝕏)
 ("`dY" ?𝕐)
 ("`dZ" ?ℤ)

 ;; Italic letters

 ("`ia" ?𝑎) ("`iA" ?𝐴)
 ("`ib" ?𝑏) ("`iB" ?𝐵)
 ("`ic" ?𝑐) ("`iC" ?𝐶)
 ("`id" ?𝑑) ("`iD" ?𝐷)
 ("`ie" ?𝑒) ("`iE" ?𝐸)
 ("`if" ?𝑓) ("`iF" ?𝐹)
 ("`ig" ?𝑔) ("`iG" ?𝐺)
 ("`ih" ?ℎ) ("`iH" ?𝐻)
 ("`ii" ?𝑖) ("`iI" ?𝐼)
 ("`ij" ?𝑗) ("`iJ" ?𝐽)
 ("`ik" ?𝑘) ("`iK" ?𝐾)
 ("`il" ?𝑙) ("`iL" ?𝐿)
 ("`im" ?𝑚) ("`iM" ?𝑀)
 ("`in" ?𝑛) ("`iN" ?𝑁)
 ("`io" ?𝑜) ("`iO" ?𝑂)
 ("`ip" ?𝑝) ("`iP" ?𝑃)
 ("`iq" ?𝑞) ("`iQ" ?𝑄)
 ("`ir" ?𝑟) ("`iR" ?𝑅)
 ("`is" ?𝑠) ("`iS" ?𝑆)
 ("`it" ?𝑡) ("`iT" ?𝑇)
 ("`iu" ?𝑢) ("`iU" ?𝑈)
 ("`iv" ?𝑣) ("`iV" ?𝑉)
 ("`iw" ?𝑤) ("`iW" ?𝑊)
 ("`ix" ?𝑥) ("`iX" ?𝑋)
 ("`iy" ?𝑦) ("`iY" ?𝑌)
 ("`iz" ?𝑧) ("`iZ" ?𝑍)
 ;; Bold italic letters

 ("`Ia" ?𝒂) ("`IA" ?𝑨)
 ("`Ib" ?𝒃) ("`IB" ?𝑩)
 ("`Ic" ?𝒄) ("`IC" ?𝑪)
 ("`Id" ?𝒅) ("`ID" ?𝑫)
 ("`Ie" ?𝒆) ("`IE" ?𝑬)
 ("`If" ?𝒇) ("`IF" ?𝑭)
 ("`Ig" ?𝒈) ("`IG" ?𝑮)
 ("`Ih" ?𝒉) ("`IH" ?𝑯)
 ("`Ii" ?𝒊) ("`II" ?𝑰)
 ("`Ij" ?𝒋) ("`IJ" ?𝑱)
 ("`Ik" ?𝒌) ("`IK" ?𝑲)
 ("`Il" ?𝒍) ("`IL" ?𝑳)
 ("`Im" ?𝒎) ("`IM" ?𝑴)
 ("`In" ?𝒏) ("`IN" ?𝑵)
 ("`Io" ?𝒐) ("`IO" ?𝑶)
 ("`Ip" ?𝒑) ("`IP" ?𝑷)
 ("`Iq" ?𝒒) ("`IQ" ?𝑸)
 ("`Ir" ?𝒓) ("`IR" ?𝑹)
 ("`Is" ?𝒔) ("`IS" ?𝑺)
 ("`It" ?𝒕) ("`IT" ?𝑻)
 ("`Iu" ?𝒖) ("`IU" ?𝑼)
 ("`Iv" ?𝒗) ("`IV" ?𝑽)
 ("`Iw" ?𝒘) ("`IW" ?𝑾)
 ("`Ix" ?𝒙) ("`IX" ?𝑿)
 ("`Iy" ?𝒚) ("`IY" ?𝒀)
 ("`Iz" ?𝒛) ("`IZ" ?𝒁)
 ;; Script letters

 ("`sa" ?𝒶) ("`sA" ?𝒜)
 ("`sb" ?𝒷) ("`sB" ?ℬ)
 ("`sc" ?𝒸) ("`sC" ?𝒞)
 ("`sd" ?𝒹) ("`sD" ?𝒟)
 ("`se" ?ℯ) ("`sE" ?ℰ)
 ("`sf" ?𝒻) ("`sF" ?ℱ)
 ("`sg" ?ℊ) ("`sG" ?𝒢)
 ("`sh" ?𝒽) ("`sH" ?ℋ)
 ("`si" ?𝒾) ("`sI" ?ℐ)
 ("`sj" ?𝒿) ("`sJ" ?𝒥)
 ("`sk" ?𝓀) ("`sK" ?𝒦)
 ("`sl" ?𝓁) ("`sL" ?ℒ)
 ("`sm" ?𝓂) ("`sM" ?ℳ)
 ("`sn" ?𝓃) ("`sN" ?𝒩)
 ("`so" ?ℴ) ("`sO" ?𝒪)
 ("`sp" ?𝓅) ("`sP" ?𝒫)
 ("`sq" ?𝓆) ("`sQ" ?𝒬)
 ("`sr" ?𝓇) ("`sR" ?ℛ)
 ("`ss" ?𝓈) ("`sS" ?𝒮)
 ("`st" ?𝓉) ("`sT" ?𝒯)
 ("`su" ?𝓊) ("`sU" ?𝒰)
 ("`sv" ?𝓋) ("`sV" ?𝒱)
 ("`sw" ?𝓌) ("`sW" ?𝒲)
 ("`sx" ?𝓍) ("`sX" ?𝒳)
 ("`sy" ?𝓎) ("`sY" ?𝒴)
 ("`sz" ?𝓏) ("`sZ" ?𝒵)
 ;; Bold script letters

 ("`Sa" ?𝓪) ("`SA" ?𝓐)
 ("`Sb" ?𝓫) ("`SB" ?𝓑)
 ("`Sc" ?𝓬) ("`SC" ?𝓒)
 ("`Sd" ?𝓭) ("`SD" ?𝓓)
 ("`Se" ?𝓮) ("`SE" ?𝓔)
 ("`Sf" ?𝓯) ("`SF" ?𝓕)
 ("`Sg" ?𝓰) ("`SG" ?𝓖)
 ("`Sh" ?𝓱) ("`SH" ?𝓗)
 ("`Si" ?𝓲) ("`SI" ?𝓘)
 ("`Sj" ?𝓳) ("`SJ" ?𝓙)
 ("`Sk" ?𝓴) ("`SK" ?𝓚)
 ("`Sl" ?𝓵) ("`SL" ?𝓛)
 ("`Sm" ?𝓶) ("`SM" ?𝓜)
 ("`Sn" ?𝓷) ("`SN" ?𝓝)
 ("`So" ?𝓸) ("`SO" ?𝓞)
 ("`Sp" ?𝓹) ("`SP" ?𝓟)
 ("`Sq" ?𝓺) ("`SQ" ?𝓠)
 ("`Sr" ?𝓻) ("`SR" ?𝓡)
 ("`Ss" ?𝓼) ("`SS" ?𝓢)
 ("`St" ?𝓽) ("`ST" ?𝓣)
 ("`Su" ?𝓾) ("`SU" ?𝓤)
 ("`Sv" ?𝓿) ("`SV" ?𝓥)
 ("`Sw" ?𝔀) ("`SW" ?𝓦)
 ("`Sx" ?𝔁) ("`SX" ?𝓧)
 ("`Sy" ?𝔂) ("`SY" ?𝓨)
 ("`Sz" ?𝔃) ("`SZ" ?𝓩)
 ;; Fraktur letters

 ("`fa" ?𝔞) ("`fA" ?𝔄)
 ("`fb" ?𝔟) ("`fB" ?𝔅)
 ("`fc" ?𝔠) ("`fC" ?ℭ)
 ("`fd" ?𝔡) ("`fD" ?𝔇)
 ("`fe" ?𝔢) ("`fE" ?𝔈)
 ("`ff" ?𝔣) ("`fF" ?𝔉)
 ("`fg" ?𝔤) ("`fG" ?𝔊)
 ("`fh" ?𝔥) ("`fH" ?ℌ)
 ("`fi" ?𝔦) ("`fI" ?ℑ)
 ("`fj" ?𝔧) ("`fJ" ?𝔍)
 ("`fk" ?𝔨) ("`fK" ?𝔎)
 ("`fl" ?𝔩) ("`fL" ?𝔏)
 ("`fm" ?𝔪) ("`fM" ?𝔐)
 ("`fn" ?𝔫) ("`fN" ?𝔑)
 ("`fo" ?𝔬) ("`fO" ?𝔒)
 ("`fp" ?𝔭) ("`fP" ?𝔓)
 ("`fq" ?𝔮) ("`fQ" ?𝔔)
 ("`fr" ?𝔯) ("`fR" ?ℜ)
 ("`fs" ?𝔰) ("`fS" ?𝔖)
 ("`ft" ?𝔱) ("`fT" ?𝔗)
 ("`fu" ?𝔲) ("`fU" ?𝔘)
 ("`fv" ?𝔳) ("`fV" ?𝔙)
 ("`fw" ?𝔴) ("`fW" ?𝔚)
 ("`fx" ?𝔵) ("`fX" ?𝔛)
 ("`fy" ?𝔶) ("`fY" ?𝔜)
 ("`fz" ?𝔷) ("`fZ" ?ℨ))

(require 'seq)

;; Quail needs alists with cons cells ‘(COM . CH)’ where COM is a LaTeX command
;; (e.g. \alpha) and CH a character (e.g. α). We define several lists extracted
;; from the ‘math-symbol-lists’ package and formatted to suit Quail’s needs.
;; NOTE we use ‘eval-when-compile’ to avoid traversing all the symbols when the
;; mode is loaded.

(defconst lambdapi--math-symbol-list-basic
  (eval-when-compile
    (let* ((cat-rx (rx (or "arrow" "greek" "Greek" "bin" "rel" "misc")))
           (pred (lambda (sym) (string-match-p cat-rx (car sym))))
           (filt (seq-filter pred math-symbol-list-basic)))
      (seq-map (lambda (sym) `(,(cadr sym) . ,(cddr sym))) filt)))
  "Extracted from ‘math-symbol-list-basic’.
Arrows, greek letters (upper and lowercase), binary relations, relations and
miscellaneous.")

(defconst lambdapi--math-symbol-list-extended
  (eval-when-compile
    (let* ((com-rx "\\Bbb.")
           (pred (lambda (sym) (string-match-p com-rx (cadr sym))))
           (filt (seq-filter pred math-symbol-list-extended)))
      (seq-map (lambda (sym) `(,(cadr sym) . ,(cdddr sym))) filt)))
  "Extracted from ‘math-symbol-list-extended’. Double struck capital letters.")

(defconst lambdapi--math-symbol-list-subscripts
  (eval-when-compile
    (seq-map (lambda (sym)
               (cons (cl-concatenate 'string "_" (cadr sym)) (cddr sym)))
             math-symbol-list-subscripts))
  "Extracted from ‘math-symbol-list-subscripts’.")

(defconst lambdapi--math-symbol-list-superscripts
  (eval-when-compile
    (seq-map (lambda (sym)
               (cons (cl-concatenate 'string "^" (cadr sym)) (cddr sym)))
             math-symbol-list-superscripts))
  "Extracted from ‘math-symbol-list-superscripts’.")

(unless lambdapi-unicode-prefer-company
  (seq-do (lambda (com-ltx) (quail-defrule (car com-ltx) (cdr com-ltx)))
          (seq-concatenate 'list
                           lambdapi--math-symbol-list-basic
                           lambdapi--math-symbol-list-extended
                           lambdapi--math-symbol-list-subscripts
                           lambdapi--math-symbol-list-superscripts)))

(provide 'lambdapi-input)
;;; lambdapi-input.el ends here
