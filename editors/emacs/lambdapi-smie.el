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
    "fail"
    "focus"
    "refine"
    "reflexivity"
    "rewrite"
    "simpl"
    "solve"
    "symmetry"
    "why3")
  "Proof tactics.")
(defconst lambdapi--queries
  '("assert"
    "assertnot"
    "compute"
    "print"
    "proofterm"
    "set"
    "type")
  "Queries.")
(defconst lambdapi--cmds
  (append
   '("inductive"
     "open"
     "require"
     "rule"
     "symbol")
   lambdapi--queries)
  "Commands at top level.")

(defun lambdapi--query-indent ()
  "Indent commands that may be in proofs.
Indent by `lambdapi-indent-basic' in proofs, and 0 otherwise."
  (save-excursion
    (forward-line -1)
    (back-to-indentation)
    (cond
     ((looking-at-p (regexp-opt (cons "begin" lambdapi--tactics)))
      `(column . ,lambdapi-indent-basic))
     ((looking-at-p (regexp-opt lambdapi--queries))
      ;; If the previous line is a query, indent similarly
      (back-to-indentation)
      `(column . ,(current-column)))
     (t '(column . 0)))))

(defconst lambdapi--smie-prec
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((ident)
      (env (ident)
           (ident ";"))
      (rw-patt)
      (args (ident)
            ("{" ident ":" sterm "}")
            ("(" ident ":" sterm ")"))
      (sterm ("TYPE")
             ("_")
             (ident)
             ("?" ident "[" env "]")    ; ?M[x;y;z]
             ("$" ident "[" env "]")    ; $X[x;y;z]
             ("`" args "," sterm)       ; binder syntax
             (sterm "→" sterm)
             ("λ" args "," sterm)
             ("λ" ident ":" sterm "," sterm)
             ("Π" args "," sterm)
             ("Π" ident ":" sterm "," sterm)
             ("let" ident "≔" sterm "in" sterm)
             ("let" ident ":" sterm "≔" sterm "in" sterm)
             ("let" args ":" sterm "≔" sterm "in" sterm)
             ("let" args "≔" sterm "in" sterm))
      (tactic ("apply" sterm)
              ("assume" sterm)
              ("fail")
              ("focus" ident)
              ("refine" sterm)
              ("reflexivity")
              ("rewrite" "[" rw-patt "]")
              ("simpl")
              ("solve")
              ("symmetry")
              ("why3"))
      (query ("assert" args "⊢" sterm ":" sterm)
             ("assert" args "⊢" sterm "≡" sterm)
             ("assertnot" args "⊢" sterm ":" sterm)
             ("assertnot" args "⊢" sterm "≡" sterm)
             ("compute" sterm)
             ("print")
             ("proofterm")
             ("set" "debug" ident)
             ("set" "flag" ident "off")
             ("set" "flag" ident "on")
             ("set" "prover" ident)
             ("set" "prover_timeout" ident)
             ("set" "verbose" ident)
             ("type" sterm))
      (prfcontent (tactic)
                  (query))
      (unif-rule-rhs
       (sterm "≡" sterm)
       ("[" unif-rule-rhs "]")
       (unif-rule-rhs ";"))
      (symdec ("symbol" args ":" sterm))
      (indcons (args ":" sterm) ("|" args ":" sterm))
      (inddec (inddec "with" args ":" sterm "≔" indcons))
      (rules (rules "with" sterm "↪" sterm))
      (command ("constant" symdec ";")
               ("injective" "inductive" inddec ";")
               ("injective" symdec ";")
               ("open" ident ";")
               ("opaque" "inductive" inddec ";")
               ("opaque" symdec ";")
               ("private" "inductive" inddec ";")
               ("private" symdec ";")
               ("begin" prfcontent "abort" ";")
               ("begin" prfcontent "admit" ";")
               ("begin" prfcontent "end" ";")
               ("protected" "inductive" inddec ";")
               ("protected" symdec ";")
               ("require" ident "as" ident ";")
               ("require" ident ";")
               ("rule" rules ";")
               ("set" "builtin" ident "≔" sterm ";")
               ("set" "infix" "left" ident "≔" sterm ";")
               ("set" "infix" "right" ident "≔" sterm ";")
               ("set" "infix" ident "≔" sterm ";")
               ("set" "prefix" ident "≔" sterm ";")
               ("set" "quantifier" ident ";")
               (query ";")
               ("set" "unif_rule" sterm "≡" sterm "↪" unif-rule-rhs ";")
               (symdec ";")))
    '((assoc ";") (assoc "≔"))
    '((assoc ";") (assoc "↪"))
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
    (`(:before . "apply") `(column . ,lambdapi-indent-basic))
    (`(:before . "assume") `(column . ,lambdapi-indent-basic))
    (`(:before . "fail") `(column . ,lambdapi-indent-basic))
    (`(:before . "focus") `(column . ,lambdapi-indent-basic))
    (`(:before . "refine") `(column . ,lambdapi-indent-basic))
    (`(:before . "reflexivity") `(column . ,lambdapi-indent-basic))
    (`(:before . "rewrite") `(column . ,lambdapi-indent-basic))
    (`(:before . "simpl") `(column . ,lambdapi-indent-basic))
    (`(:before . "solve") `(column . ,lambdapi-indent-basic))
    (`(:before . "symmetry") `(column . ,lambdapi-indent-basic))
    (`(:before . "why3") `(column . ,lambdapi-indent-basic))
    
    (`(:before . ,(or "admit" "abort" "end")) '(column . 0))
    (`(:after . ,(or "admit" "abort" "end")) '(column . 0))

    (`(:before . ,(or "assert" "assertnot" "compute" "print" "proofterm"
                      "set" "type"))
     (lambdapi--query-indent))

    (`(,_ . ,(or "," "↪" "→" "≡")) (smie-rule-separator kind))

    (`(,(or :before :list-intro) . ,(or "≔" ":")) (smie-rule-separator kind))
    (`(:after . ,(or "≔" ":")) lambdapi-indent-basic)

    (`(:list-intro . ,(or "with" "rule" "λ" "Π" "begin")) t)
    (`(:after . "begin") lambdapi-indent-basic)
    (`(:after . ,(or "rule" "with")) (* 2 lambdapi-indent-basic))
    (`(:after . "in") (smie-rule-parent))
    (`(:after . ,(or "symbol" "inductive")) lambdapi-indent-basic)
    (`(:after . ,(or "apply" "assume" "fail" "focus" "refine" "reflexivity"
                     "rewrite" "simpl" "solve" "symmetry" "why3"))
     lambdapi-indent-basic)

    ;; Toplevel
    (`(:before . "protected") '(column . 0))
    (`(:before . "private") '(column . 0))
    (`(:before . "injective") '(column . 0))
    (`(:before . "constant") '(column . 0))
    (`(:before . "require") '(column . 0))
    (`(:before . "open") '(column . 0))
    (`(:before . "inductive") '(column . 0))
    (`(:before . "symbol") '(column . 0))
    (`(:before . "begin") '(column . 0))
    (`(:before . ,(or "with" "rule")) '(column . 0))))

(provide 'lambdapi-smie)
;;; lambdapi-smie.el ends here
