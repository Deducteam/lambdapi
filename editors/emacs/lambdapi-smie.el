;;; lambdapi-smie.el --- Indentation for lambdapi -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Gabriel Hondet
;;
;; Author: Gabriel Hondet
;; Package-Requires: ((emacs 26.1) (smie))
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;; Many thanks to Nim and Nim mode
;; TODO: refine editing of proofs, perhaps make a single token PRFTAC for
;; tactics, adjust backward parsing (greed and lookahead of `looking-back`) to
;; avoid finding token `in` in `refine` and `definition`.
;; TODO: escaped identifier
;;; Code:
(require 'smie)

(defconst lambdapi--rx-ident "[a-zA-Z_][a-zA-Z0-9_]*")
(defconst lambdapi--rx-natlit "[0-9]+")
(defconst lambdapi--rx-floatlit "[0-9]+\\([.][0-9]+\\)?")
(defconst lambdapi--rx-stringlit "\"[^\"\n]\"")
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
(defconst lambdapi--prf-finish '("abort" "admit" "qed"))
(defconst lambdapi--punctuation '("[" "]" "|" ")" "(" "{" "}" "." ":"))
(defconst lambdapi--keywords
  '("let"
    "in"
    "λ"
    "∀"
    ","
    "⇒"
    "TYPE"
    "≔"
    "→"
    "≔"
    "symbol"
    "private"
    "protected"
    "injective"
    "constant"
    "theorem"
    "proof"
    "definition"
    "rule"
    "and"
    "assert"
    "assertnot"
    "type"
    "compute"
    "set"
    "verbose"
    "prefix"
    "infix"
    "left"
    "right"
    "prover"
    "prover_timeout"
    "require"
    "open"
    "as"))

(defconst lambdapi--smie-prec
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((ident ("ID"))
      (qident (ident)
              (qident "." ident))
      (rw-patt)
      (args (ident)
            ("{" ident ":" sterm "}")
            ("(" ident ":" sterm ")"))
      (sterm ("TYPE")
             ("_")
             (ident)
             (sterm "⇒" sterm)
             ("λ" args "," sterm)
             ("∀" args "," sterm)
             ("let" args "≔" sterm "in" sterm))
      (tactic ("refine" sterm)
              ("assume" sterm)
              ("apply" sterm)
              ("simpl")
              ("rewrite" "[" rw-patt "]" sterm)
              ("reflexivity")
              ("focus" nat-lit)
              ("print")
              ("proofterm")
              ("why3"))
      (rule (sterm "→" sterm))
      (rules (rule)
             (rule "and" rule))
      ; TODO: token SYMTAG?
      (symtag ("constant" "injective" "protected" "private"))
      (command (symtag "symbol" args ":" sterm)
               ("theorem" args ":" sterm "proof" tactic "PRFEND")
               ("definition" args "≔" sterm)
               ("rule" rules)

               ("assert" sterm "≡" sterm)
               ("assert" sterm ":" sterm)
               ("assertnot" sterm ":" sterm)
               ("assertnot" sterm "≡" sterm)
               ("compute" sterm)
               ("type" sterm)

               ("require" qident)
               ("require" "open" qident)
               ("require" qident "as" ident)
               ("require" "open" qident)

               ("set" "verbose" "NATLIT")
               ("set" "debug" ident)
               ("set" "builtin" "STRINGLIT" "≔" qident)
               ("set" "prefix" "FLOATLIT" "STRINGLIT" "≔" qident)
               ("set" "infix" "FLOATLIT" ident "≔" qident)
               ("set" "infix" "left" "FLOATLIT" ident "≔" qident)
               ("set" "infix" "right" "FLOATLIT" ident "≔" qident)
               ("set" "prover") ; no stringlit because of conflict
               ("set" "prover_timeout" "NATLIT")
               ("set" "declared" ident)))
    '((assoc ",") (assoc "in") (assoc "⇒")))))

;; TODO: literals with double quotes for set infix etc
(defun lambdapi--smie-forward-token ()
  "Forward lexer for Dedukti3."
  ;; Skip comments
  (forward-comment (point-max))
  (cond
   ;; qed, admit or abort as "PRFEND"
   ((looking-at (regexp-opt '("qed" "admit" "abort")))
    (goto-char (match-end 0))
    "PRFEND")
   ((looking-at (regexp-opt (append lambdapi--keywords
                                    lambdapi--tactics
                                    lambdapi--punctuation)))
    (goto-char (match-end 0))
    (match-string-no-properties 0))
   ;; nat lit
   ((looking-at lambdapi--rx-natlit)
    (goto-char (match-end 0))
    "NATLIT")
   ;; float lit
   ((looking-at lambdapi--rx-floatlit)
    (goto-char (match-end 0))
    "FLOATLIT")
   ;; string lit
   ((looking-at lambdapi--rx-stringlit)
    (goto-char (match-end 0))
    "STRINGLIT")
   ;; identifiers
   ((looking-at lambdapi--rx-ident)
    (goto-char (match-end 0))
    "ID")
   (t (buffer-substring-no-properties
       (point)
       (progn (skip-syntax-forward "w_")
              (point))))))

(defun lambdapi--smie-backward-token ()
  "Backward lexer for Dedukti3."
  (forward-comment (- (point)))
  (cond
   ((looking-back (regexp-opt
                   (append lambdapi--keywords
                           lambdapi--tactics
                           lambdapi--punctuation))
                  (- (point) 14) t)
    (goto-char (match-beginning 0))
    (match-string-no-properties 0))
   ;; naturals
   ((looking-back lambdapi--rx-natlit nil t)
    (goto-char (match-beginning 0))
    "NATLIT")
   ;; floats
   ((looking-back lambdapi--rx-floatlit nil t)
    (goto-char (match-beginning 0))
    "FLOATLIT")
   ((looking-back lambdapi--rx-stringlit nil t)
    (goto-char (match-beginning 0))
    "STRINGLIT")
   ;; identifiers
   ((looking-back lambdapi--rx-ident nil t)
    (goto-char (match-beginning 0))
    "ID")
   (t (buffer-substring-no-properties
       (point)
       (progn (skip-syntax-backward "w_")
              (point))))))

(defvar lambdapi-indent-basic 2
  "Basic indentation for lambdapi-mode.")

(defun lambdapi--smie-rules (kind token)
  "Indentation rule for case KIND and token TOKEN."
  (pcase (cons kind token)
    (`(:elem . basic) 0)
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
    (`(:before . "PRFEND") '(column . 0))
    (`(:after . "PRFEND") '(column . 0))

    (`(:before . "protected") '(column . 0))
    (`(:before . "private") '(column . 0))
    (`(:before . "injective") '(column . 0))
    (`(:before . "constant") '(column . 0))
    ;; Toplevel
    (`(:before . "compute") '(column . 0))
    (`(:before . "type") '(column . 0))
    (`(:before . "assert") '(column . 0))
    (`(:before . "assertnot") '(column . 0))

    (`(:before . "require") '(column . 0))
    (`(:before . "set") '(column . 0))

    (`(:before . "definition") '(column . 0))
    (`(:before . "theorem") '(column . 0))
    (`(:before . "proof") '(column . 0))
    (`(:before . "PRFEND") '(column . 0))
    (`(:before . "symbol") '(column . 0))
    (`(:before . "rule") '(column . 0))
    (`(:before . "and") '(column . 1))))

;; DEBUG
(defun dedukti-backward ()
  "Move backward by one token or by a sexp."
  (interactive)
  (let ((beg (point)))
    (prog1
        (or (lambdapi--smie-backward-token)
            (backward-sexp))
      (when (eq beg (point))
        (backward-char)))))

(defun dedukti-smie-backward-debug ()
  "Print the current value of `dedukti-smie-backward-token'."
  (interactive)
  (let ((v (dedukti-backward)))
    (when v (princ v))))

(provide 'lambdapi-smie)
;;; lambdapi-smie.el ends here
