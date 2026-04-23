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
    "apply"
    "assume"
    "fail"
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
    (term ("TYPE")
          ("_")
          (ident)
          ("?" ident "[" env "]")
          ("$" ident "[" env "]")
          ("`" ident args "," term)
          (term "→" term)
          ("λ" args "," term)
          ("λ" ident ":" term "," term)
          ("Π" args "," term)
          ("Π" ident ":" term "," term)
          ("let" ident "≔" term "in" term)
          ("let" ident ":" term "≔" term "in" term)
          ("let" args ":" term "≔" term "in" term)
          ("let" args "≔" term "in" term))
    (option ("on") ("off"))
    (equation (term "≡" term))
    (typing (term ":" term))
    (assert (equation) (typing))
    (query ("assert" args "⊢" assert)
           ("assertnot" args "⊢" assert)
           ("compute" term)
           ("debug" ident)
           ("flag" ident option)
           ("print")
           ("proofterm")
           ("prover" ident)
           ("prover_timeout" ident)
           ("search" term)
           ("type" term)
           ("verbose" ident))
    (tactic (query)
            ("apply" term)
            ("assume" term)
            ("change" term)
            ("eval" term)
            ("fail")
            ("focus" ident)
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
            ("simplify")
            ("simplify" ident)
            ("simplify" "rule" "off")
            ("solve")
            ("symmetry")
            ("try" tactic)
            ("why3"))
    (proof (tactic) (tactic ";" tactic))
    (modifier ("associative")
              ("commutative")
              ("constant")
              ("injective")
              ("opaque")
              ("private")
              ("protected")
              ("sequential"))
    (modifiers (modifier modifiers))
    (constructor (args ":" term))
    (constructors (constructor) (constructors "|" constructors))
    (inductive (ident args ":" term "≔" constructors))
    (inductives (inductive) (inductives "with" inductives))
    (rule (term "↪" term))
    (rules (rule) (rules "with" rules))
    (side ("left")
          ("right"))
    (notation (infix term)
              (infix side term)
              ("prefix" term)
              ("postfix" term)
              ("quantifier"))
    (proofend ("abort") ("admitted") ("end"))
    (definition ("≔" term)
                ("≔" term "begin" proof proofend))
    (unif-rule-rhs (equation) (unif-rule-rhs ";" unif-rule-rhs))
    (reqopen ("require" ident)
             ("require" ident "as" iden)
             ("require" "open" ident)
             ("require" "private" "open" ident)
             ("open" ident)
             ("private" "open" ident))
    (command (reqopen)
             (query)
             (modifiers "symbol" args ":" term)
             (modifiers "symbol" args ":" term definition)
             (modifiers "inductive" inductive)
             ("notation" ident notation)
             ("builtin" ident "≔" term)
             ("rule" rules)
             ("coerce_rule" rule)
             ("unif_rule" equation "↪" "[" unif-rule-rhs "]"))
    (commands (command) (commands ";" commands))
    )
  )

(defconst lambdapi--smie-prec
  (smie-prec2->grammar
   (smie-bnf->prec2
    lambdapi-smie-bnf
    '((assoc ";"))
    '((assoc "with"))
    '((assoc ","))
    '((assoc "→")))))

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
    (`(:before . "change") `(column . ,lambdapi-indent-basic))
    (`(:before . "eval") `(column . ,lambdapi-indent-basic))
    (`(:before . "fail") `(column . ,lambdapi-indent-basic))
    (`(:before . "focus") `(column . ,lambdapi-indent-basic))
    (`(:before . "generalize") `(column . ,lambdapi-indent-basic))
    (`(:before . "have") `(column . ,lambdapi-indent-basic))
    (`(:before . "induction") `(column . ,lambdapi-indent-basic))
    (`(:before . "orelse") `(column . ,lambdapi-indent-basic))
    (`(:before . "refine") `(column . ,lambdapi-indent-basic))
    (`(:before . "reflexivity") `(column . ,lambdapi-indent-basic))
    (`(:before . "remove") `(column . ,lambdapi-indent-basic))
    (`(:before . "repeat") `(column . ,lambdapi-indent-basic))
    (`(:before . "rewrite") `(column . ,lambdapi-indent-basic))
    (`(:before . "set") `(column . ,lambdapi-indent-basic))
    (`(:before . "simplify") `(column . ,lambdapi-indent-basic))
    (`(:before . "solve") `(column . ,lambdapi-indent-basic))
    (`(:before . "symmetry") `(column . ,lambdapi-indent-basic))
    (`(:before . "try") `(column . ,lambdapi-indent-basic))
    (`(:before . "why3") `(column . ,lambdapi-indent-basic))

    (`(:before . ,(or "abort" "admitted" "end")) '(column . 0))
    (`(:after . ,(or "abort" "admitted" "end")) '(column . 0))

    (`(:before . ,(or "assert" "assertnot" "compute"
                      "print" "proofterm" "search" "type"))
     (lambdapi--query-indent))

    (`(,_ . ,(or "," "↪" "→" "≡")) (smie-rule-separator kind))

    (`(,(or :before :list-intro) . ,(or "≔" ":")) (smie-rule-separator kind))
    (`(:after . ,(or "≔" ":")) lambdapi-indent-basic)

    (`(:list-intro . ,(or "with" "rule" "λ" "Π" "begin")) t)
    (`(:after . "begin") lambdapi-indent-basic)
    (`(:after . ,(or "rule" "with" "coerce_rule" "unif_rule"))
     (* 2 lambdapi-indent-basic))
    (`(:after . "in") (smie-rule-parent))
    (`(:after . ,(or "symbol" "inductive")) lambdapi-indent-basic)
    (`(:after . ,(or "apply" "assume" "change" "eval" "fail" "focus"
                     "generalize" "have" "induction" "refine" "reflexivity"
                     "remove" "rewrite" "set" "simplify" "solve" "symmetry"
                     "why3"))
     lambdapi-indent-basic)

    ;; Toplevel
    (`(:before . "associative") '(column . 0))
    (`(:before . "begin") '(column . 0))
    (`(:before . "builtin") '(column . 0))
    (`(:before . "coerce_rule") '(column . 0))
    (`(:before . "commutative") '(column . 0))
    (`(:before . "constant") '(column . 0))
    (`(:before . "debug") '(column . 0))
    (`(:before . "flag") '(column . 0))
    (`(:before . "inductive") '(column . 0))
    (`(:before . "injective") '(column . 0))
    (`(:before . "notation") '(column . 0))
    (`(:before . "open") '(column . 0))
    (`(:before . "private") '(column . 0))
    (`(:before . "protected") '(column . 0))
    (`(:before . "rule") '(column . 0))
    (`(:before . "require") '(column . 0))
    (`(:before . "symbol") '(column . 0))
    (`(:before . "unif_rule") '(column . 0))
    (`(:before . "verbose") '(column . 0))
    (`(:before . "with") '(column . 0))))

(provide 'lambdapi-smie)
;;; lambdapi-smie.el ends here
