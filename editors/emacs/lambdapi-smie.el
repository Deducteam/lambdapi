;;; lambdapi-smie.el --- Indentation for lambdapi -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CECILL-2.1
;;; Commentary:
;;
;;; Code:
(require 'lambdapi-vars)
(require 'smie)

;; Lists of keywords
(defconst lambdapi--tactics
  '("admit"
    "all_hyps"
    "apply"
    "assume"
    "assumption"
    "fail"
    "first_hyp"
    "focus"
    "generalize"
    "have"
    "induction"
    "orelse"
    "refine"
    "reflexivity"
    "remove"
    "repeat"
    "rewrite"
    "set"
    "simplify"
    "solve"
    "symmetry"
    "try"
    "why3")
  "Proof tactics.")
(defconst lambdapi--queries
  '("assert"
    "assertnot"
    "compute"
    "print"
    "proofterm"
    "search"
    "type")
  "Queries.")
(defconst lambdapi--cmds
  (append
   '("builtin"
     "coerce_rule"
     "debug"
     "flag"
     "inductive"
     "notation"
     "open"
     "prover"
     "prover_timeout"
     "require"
     "rule"
     "symbol"
     "unif_rule"
     "verbose")
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

(defconst lambdapi-smie-bnf
  '((ident)
      (env (ident)
           (env ";" env))
      (rw-patt)
      (args (ident)
            ("{" ident ":" term "}")
            ("(" ident ":" term ")"))
      (simplify-args (ident)
             (rule "off"))
      (term ("TYPE")
             ("_")
             (ident)
             ("?" ident "[" env "]")
             ("$" ident "[" env "]")
;;             ("`" ident args "," term)
             (term "→" term)
             ("λ" args "," term)
             ("λ" ident ":" term "," term)
             ("Π" args "," term)
             ("Π" ident ":" term "," term)
             ("let" ident "≔" term "in" term)
             ("let" ident ":" term "≔" term "in" term)
             ("let" args ":" term "≔" term "in" term)
             ("let" args "≔" term "in" term))
      (equation (term "≡" term))
      (typing (term ":" term))
      (assert (equation) (typing))
      (query ("assert" args "⊢" assert)
             ("assertnot" args "⊢" assert)
             ("compute" term)
             ("debug" ident)
             ("flag" ident "on")
             ("flag" ident "off")
             ("print")
             ("proofterm")
             ("prover" ident)
             ("prover_timeout" ident)
             ("search" term)
             ("type" term)
             ("verbose" ident))
      (tactic (query)
              ("all_hyps" term)
              ("apply" term)
              ("assume" term)
              ("assumption")
              ("change" term)
              ("eval" term)
              ("fail")
              ("first_hyp" term)
              ("focus" term)
              ("generalize" ident)
              ("have" ident ":" term)
              ("induction")
              ("orelse" tactic)
              ("refine" term)
              ("reflexivity")
              ("remove" ident)
              ("repeat" tactic)
              ("rewrite" "[" rw-patt "]")
              ("set" ident "≔" term)
              ("simplify" simplify-args)
              ("solve")
              ("symmetry")
              ("try" tactic)
              ("why3"))
      (proof (tactic) (tactic ";" tactic))
      ;; TODO : define more finely modifiers to allow only accepted modifiers
      ;; without raising warning token ??? is both opener and neither
      ;; or error : Adjacent non-terminals: modifier modifiers
      (modifier)
      (modifiers ("associative" modifier)
                 ("commutative" modifier)
                 ("constant" modifier)
                 ("injective" modifier)
                 ("opaque" modifier)
                 ("private" modifier)
                 ("protected" modifier)
                 ("sequential" modifier))
      (constructor (args ":" term))
      (constructors (constructor) (constructors "|" constructors))
      ;; FIX ME : should be term args but raises an error Adjacent non-terminals
      (ident_args)
      (inductive (ident_args ":" term "≔" constructors))
      (winductives (inductive)
                   (inductive "with" winductives))
      (inductives (inductive) (inductive "with" winductives))
      (rule (term "↪" term))
      (rules (rule) (rules "with" rules))
      (unif-rule-rhs (equation) (unif-rule-rhs ";" unif-rule-rhs))
      (open-command ("open" ident))
      (popen   ("private" open-command)
               (open-command))
      (reqopen ("require" ident)
               ("require" ident "as" ident)
               ("require" open-command)
               (open-command)
               ("require" popen)
               (popen))
      (command (reqopen)
               (query)
               (modifiers "symbol" args ":" term)
               (modifiers "symbol" args ":" term ("≔" term))
               (modifiers "symbol" args ":" term "≔" term "begin" proof "abort")
               (modifiers "symbol" args ":" term "≔" term "begin" proof "admitted")
               (modifiers "symbol" args ":" term "≔" term "begin" proof "end")
               (modifiers "inductive" inductive)
               ("builtin" ident "≔" term)
               ("notation" ident "infix" "left" term)
               ("notation" ident "infix" "right" term)
               ("notation" ident "infix" term)
               ("notation" ident "prefix" term)
               ("notation" ident "postfix" term)
               ("notation" ident "quantifier")
               ("rule" rules)
               ("coerce_rule" rule)
               ("unif_rule" equation "↪" "[" unif-rule-rhs "]"))
      (commands (command) (commands ";" commands))))

(defconst lambdapi--smie-prec
  (smie-prec2->grammar
   (smie-bnf->prec2
    lambdapi-smie-bnf
    '((assoc "|"))
    '((assoc "with"))
    '((assoc ";"))
    '((assoc "coerce_rule") (assoc "↪"))
    ;; FIX ME : Check priority rules
    '((assoc "≡") (assoc "↪"))
    '((assoc "unif_rule") (assoc "≡"))
    '((assoc ",") (assoc "in") (assoc "→"))
  )))

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

;;    (`(:list-intro . "begin") t)
    (`(:after . "begin") lambdapi-indent-basic)
    (`(:after . ":") lambdapi-indent-basic)
    (`(:after . ,(or "require" "open")) lambdapi-indent-basic)
    (`(:before . "with") (smie-rule-parent))
;;    (`(:before . "with") '(column . 0))
))

(provide 'lambdapi-smie)
;;; lambdapi-smie.el ends here
