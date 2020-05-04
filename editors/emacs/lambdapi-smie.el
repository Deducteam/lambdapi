;;; lambdapi-smie.el --- Indentation for lambdapi -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
;;; Commentary:
;;
;;; Code:
(require 'lambdapi-vars)
(require 'smie)

;; Lists of keywords
(defconst lambdapi--tactics
  '("apply"
    "assume"
    "focus"
    "print"
    "proofterm"
    "refine"
    "reflexivity"
    "rewrite"
    "simpl"
    "symmetry"
    "why3"))
(defconst lambdapi--queries '("set" "assert" "assertnot" "type" "compute")
  "Commands that can appear in proofs.")
(defconst lambdapi--cmds
  (append '("symbol" "theorem" "rule" "and" "definition" "proof" "require")
          lambdapi--queries)
  "Commands at top level.")

(defun lambdapi--previous-cmd ()
  "Return the previous command used in the file."
  (save-excursion
    (while
        (progn
          (back-to-indentation)
          (not (looking-at (regexp-opt lambdapi--cmds))))
      (forward-line -1)))
  (match-string 0))

(defun lambdapi--colon-indent ()
  "Indent before colon."
  (let ((ppss (syntax-ppss)))
    (when (and (= 0 (nth 0 ppss)) (smie-rule-bolp))
      '(column 0)))) ; At beginning of line if not inside parentheses

(defun lambdapi--query-indent ()
  "Indent commands that may be in proofs.
Indent by `lambdapi-indent-basic' in proofs, and 0 otherwise."
  (save-excursion
    (forward-line -1)
    (back-to-indentation)
    (cond
     ;; Perhaps `(smie-rule-parent)' would be enough here
     ((looking-at-p (regexp-opt (cons "proof" lambdapi--tactics)))
      `(column . ,lambdapi-indent-basic))
     ((looking-at-p (regexp-opt lambdapi--queries))
      (smie-rule-parent))
     (t '(column . 0)))))

(defconst lambdapi--smie-prec
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((ident)
      (env (ident)
           (csidentl "," ident))
      (rw-patt)
      (args (ident)
            ("{" ident ":" sterm "}")
            ("(" ident ":" sterm ")"))
      (sterm ("TYPE")
             ("_")
             (ident)
             ("?" ident "[" env "]") ;; ?M[x,y,z]
             ("$" ident "[" env "]") ;; $X[x,y,z]
             (sterm "→" sterm)
             ("λ" args "," sterm)
             ("λ" ident ":" sterm "," sterm)
             ("Π" args "," sterm)
             ("Π" ident ":" sterm "," sterm)
             ("let" ident "≔" sterm "in" sterm)
             ("let" ident ":" sterm "≔" sterm "in" sterm)
             ("let" args ":" sterm "≔" sterm "in" sterm)
             ("let" args "≔" sterm "in" sterm))

      (tactic ("refine" sterm)
              ("assume" sterm)
              ("apply" sterm)
              ("simpl")
              ("rewrite" "[" rw-patt "]")
              ("reflexivity")
              ("focus" ident)
              ("print")
              ("proofterm")
              ("why3"))
      (query ("assert" sterm "≡" sterm)
             ("assert" sterm ":" sterm)
             ("assertnot" sterm ":" sterm)
             ("assertnot" sterm "≡" sterm)
             ("compute" sterm)
             ("type" sterm)

             ("set" "prover" ident) ; no stringlit because of conflict
             ("set" "prover_timeout" ident)
             ("set" "verbose" ident)
             ("set" "debug" ident)
             ("set" "flag" ident "on")
             ("set" "flag" ident "off"))

      (prfcontent (tactic)
                  (query))
      (unif-rule-rhs (sterm "≡" sterm)
                     (unif-rule-rhs "," sterm "≡" sterm))
      (symdec ("symbol" args ":" sterm))
      (command ("injective" symdec)
               ("constant" symdec)
               ("private" symdec)
               ("protected" symdec)
               (symdec)
               ("theorem" args ":" sterm)
               ("proof" prfcontent "qed")
               ("proof" prfcontent "admit")
               ("proof" prfcontent "abort")
               ("definition" args "≔" sterm)

               ("rule" sterm "↪" sterm)
               ("with" sterm "↪" sterm)

               ("require" ident)
               ("open" ident)
               ("require" ident "as" ident)

               ("set" "unif_rule" sterm "≡" sterm "↪" unif-rule-rhs)
               ("set" "builtin" ident "≔" ident)
               ("set" "prefix" ident "≔" ident)
               ("set" "infix" ident "≔" ident)
               ("set" "infix" "left" ident "≔" ident)
               ("set" "infix" "right" ident "≔" ident)
               ("set" "declared" ident)))
    '((assoc "≡") (assoc ",") (assoc "in") (assoc "→")))))

(defun lambdapi--smie-forward-token ()
  "Forward lexer for Dedukti3."
  (smie-default-forward-token))

(defun lambdapi--smie-backward-token ()
  "Backward lexer for Dedukti3.
The default lexer is used because the syntax is primarily made of sexps."
  (smie-default-backward-token))

(defun lambdapi--smie-rules (kind token)
  "Indentation rule for case KIND and token TOKEN."
  (pcase (cons kind token)
    (`(:elem . basic) 0)

    (`(:list-intro . ,(or "require" "open")) t)
    (`(:after . ,(or "require" "open")) lambdapi-indent-basic)

    ;; tactics
    (`(:before . "simpl") `(column . ,lambdapi-indent-basic))
    (`(:before . "rewrite") `(column . ,lambdapi-indent-basic))
    (`(:before . "assume") `(column . ,lambdapi-indent-basic))
    (`(:before . "apply") `(column . ,lambdapi-indent-basic))
    (`(:before . "refine") `(column . ,lambdapi-indent-basic))
    (`(:before . "why3") `(column . ,lambdapi-indent-basic))
    (`(:before . "reflexivity") `(column . ,lambdapi-indent-basic))
    (`(:before . "focus") `(column . ,lambdapi-indent-basic))
    (`(:before . "print") `(column . ,lambdapi-indent-basic))

    (`(:before . ,(or "admit" "abort" "qed")) '(column . 0))
    (`(:after . ,(or "admit" "abort" "qed")) '(column . 0))

    (`(:before . ,(or "set" "compute" "type" "assert" "assertnot"))
     (lambdapi--query-indent))

    (`(,_ . ,(or "≔" "," "↪" "→" ":" "≡")) (smie-rule-separator kind))

    (`(:list-intro . ,(or "with" "rule" "λ" "Π" "proof")) t)
    (`(:after . "proof") lambdapi-indent-basic)
    (`(:after . ,(or "rule" "with")) (* 2 lambdapi-indent-basic))
    (`(:after . "in") (smie-rule-parent))
    (`(:after . ,(or "symbol" "definition" "theorem")) lambdapi-indent-basic)
    (`(:after . ,(or "simpl" "rewrite" "assume" "apply" "refine"
                     "why3" "reflexivity" "focus" "print"))
      lambdapi-indent-basic)

    ;; Toplevel
    (`(:before . "protected") '(column . 0))
    (`(:before . "private") '(column . 0))
    (`(:before . "injective") '(column . 0))
    (`(:before . "constant") '(column . 0))
    (`(:before . "require") '(column . 0))
    (`(:before . "open") '(column . 0))
    (`(:before . "definition") '(column . 0))
    (`(:before . "theorem") '(column . 0))
    (`(:before . "proof") '(column . 0))
    (`(:before . "symbol") '(column . 0))

    (`(:before . ,(or "with" "rule")) '(column . 0))))

(provide 'lambdapi-smie)
;;; lambdapi-smie.el ends here
