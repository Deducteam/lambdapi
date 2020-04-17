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

 ;; Lambdapi syntax

 ("\\rightarrow" ?→) ("->" ?→)
 ("\\hookrightarrow" ?↪) ("-->" ?↪)
 ("\\\\" ?λ)
 ("\\defeq" ?≔) (":=" ?≔)
 ("\\equiv" ?≡) ("==" ?≡)
 ("\\vdash" ?⊢) ("|-" ?⊢)

 ;; Logical connectors

 ("\\wedge" ?∧) ("\\and" ?∧) ("&&" ?∧) ("/\\" ?∧)
 ("\\vee" ?∨) ("\\or" ?∨) ("||" ?∨) ("\\/" ?∨)
 ("\\implies" ?⇒) ("=>" ?⇒)
 ("\\neg" ?¬) ("~~" ?¬)
 ("\\forall" ?∀) ("!!" ?∀)
 ("\\exists" ?∃) ("??" ?∃)
 ("\\supset" ?⊃) ("=)" ?⊃)
 ("\\is_equiv" ?⇔)

  ;; Miscellaneous

 ("\\Box" ?□) ("[]" ?□)
 ("::" ?⸬)

 ;; Subscripts

 ("_0" ?₀) ("_1" ?₁) ("_2" ?₂) ("_3" ?₃) ("_4" ?₄)
 ("_5" ?₅) ("_6" ?₆) ("_7" ?₇) ("_8" ?₈) ("_9" ?₉)
 ("_+" ?₊) ("_-" ?₋) ("_=" ?₌) ("_(" ?₍) ("_)" ?₎)
 ("_a" ?ₐ) ("_e" ?ₑ) ("_h" ?ₕ) ("_i" ?ᵢ) ("_j" ?ⱼ)
 ("_k" ?ₖ) ("_l" ?ₗ) ("_m" ?ₘ) ("_n" ?ₙ) ("_o" ?ₒ)
 ("_p" ?ₚ) ("_r" ?ᵣ) ("_s" ?ₛ) ("_t" ?ₜ) ("_u" ?ᵤ)
 ("_v" ?ᵥ) ("_x" ?ₓ)
  
 ;; Superscripts

 ("^0" ?⁰) ("^1" ?¹) ("^2" ?²) ("^3" ?³) ("^4" ?⁴)
 ("^5" ?⁵) ("^6" ?⁶) ("^7" ?⁷) ("^8" ?⁸) ("^9" ?⁹)
 ("^+" ?⁺) ("^-" ?⁻) ("^=" ?⁼) ("^(" ?⁽) ("^)" ?⁾)
 ("^a" ?ᵃ) ("^b" ?ᵇ) ("^c" ?ᶜ) ("^d" ?ᵈ) ("^e" ?ᵉ)
 ("^f" ?ᶠ) ("^g" ?ᵍ) ("^h" ?ʰ) ("^i" ?ⁱ) ("^j" ?ʲ)
 ("^k" ?ᵏ) ("^l" ?ˡ) ("^m" ?ᵐ) ("^n" ?ⁿ) ("^o" ?ᵒ)
 ("^p" ?ᵖ) ("^r" ?ʳ) ("^s" ?ˢ) ("^t" ?ᵗ) ("^u" ?ᵘ)
 ("^v" ?ᵛ) ("^w" ?ʷ) ("^x" ?ˣ) ("^y" ?ʸ) ("^z" ?ᶻ)
 ("^A" ?ᴬ) ("^B" ?ᴮ) ("^D" ?ᴰ) ("^E" ?ᴱ) ("^G" ?ᴳ)
 ("^H" ?ᴴ) ("^I" ?ᴵ) ("^J" ?ᴶ) ("^K" ?ᴷ) ("^L" ?ᴸ)
 ("^M" ?ᴹ) ("^N" ?ᴺ) ("^O" ?ᴼ) ("^P" ?ᴾ) ("^R" ?ᴿ)
 ("^T" ?ᵀ) ("^U" ?ᵁ) ("^V" ?ⱽ) ("^W" ?ᵂ)
  
 ;; Greek letters

 ("\\alpha" ?α) ("`a" ?α)
 ("\\beta" ?β) ("`b" ?β)
 ("\\gamma" ?γ) ("`c" ?γ) ("\\Gamma" ?Γ) ("`C" ?Γ)
 ("\\delta" ?δ) ("`d" ?δ) ("\\Delta" ?Δ) ("`D" ?Δ)
 ("\\epsilon" ?ϵ) ("`e" ?ε)
 ("\\zeta" ?ζ) ("`z" ?ζ)
 ("\\eta" ?η) ("`h" ?η)
 ("\\theta" ?θ)
 ("\\iota" ?ι) ("`i" ?ι)
 ("\\kappa" ?κ) ("`k" ?κ)
 ("\\lambda" ?λ) ("`l" ?λ) ("\\Lambda" ?Λ) ("`L" ?Λ)
 ("\\mu" ?μ) ("`m" ?μ)
 ("\nu" ?ν) ("`n" ?ν)
 ("\\xi" ?ξ) ("\\Xi" ?Ξ)
 ("\\omicron" ?ο)
 ("\\pi" ?π) ("`p" ?π) ("\\Pi" ?Π) ("`P" ?Π)
 ("\\rho" ?ρ) ("`r" ?ρ)
 ("\\sigma" ?σ) ("`s" ?σ) ("\\Sigma" ?Σ) ("`S" ?Σ)
 ("\\tau" ?τ) ("`t" ?τ)
 ("\\upsilon" ?υ) ("`u" ?υ) ("\\Upsilon" ?ϒ) ("`U" ?ϒ)
 ("\\phi" ?φ) ("\\Phi" ?Φ)
 ("\\chi" ?χ) ("`x" ?χ)
 ("\\omega" ?ω) ("`w" ?ω) ("\\omega" ?Ω) ("`w" ?Ω)
 ("\\psi" ?ψ) ("\\Psi" ?Ψ)

 ;; Double-struck letters

 ("`bA" ?𝔸)
 ("`bB" ?𝔹)
 ("`bC" ?ℂ)
 ("`bD" ?𝔻)
 ("`bE" ?𝔼)
 ("`bF" ?𝔽)
 ("`bG" ?𝔾)
 ("`bH" ?ℍ)
 ("`bI" ?𝕀)
 ("`bJ" ?𝕁)
 ("`bK" ?𝕂)
 ("`bL" ?𝕃)
 ("`bM" ?𝕄)
 ("`bN" ?ℕ)
 ("`bO" ?𝕆)
 ("`bP" ?ℙ)
 ("`bQ" ?ℚ)
 ("`bR" ?ℝ)
 ("`bS" ?𝕊)
 ("`bT" ?𝕋)
 ("`bU" ?𝕌)
 ("`bV" ?𝕍)
 ("`bW" ?𝕎)
 ("`bX" ?𝕏)
 ("`bY" ?𝕐)
 ("`bZ" ?ℤ)

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
 ("`fz" ?𝔷) ("`fZ" ?ℨ)
 )

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
