;;; lambdapi-vars.el --- Variables for lambadpi-mode -*- lexical-binding: t; -*-
;;; Commentary:
;;
;; The lists defined are mainly used for syntax colouring and completion.
;;
;;; Code:
(defconst lambdapi-tactics
  '("apply"
    "assume"
    "print"
    "proofterm"
    "refine"
    "reflexivity"
    "rewrite"
    "simpl"
    "symmetry"
    "why3")
  "Proof tactics.")

(defconst lambdapi-sig-commands
  '("and"
    "definition"
    "in"
    "let"
    "proof"
    "qed"
    "require"
    "rule"
    "symbol"
    "theorem")
  "Commands that enrich the signature.")

(defconst lambdapi-warning
  '("abort" "admit")
  "To be displayed in red.")

(defconst lambdapi-misc-commands
  '("type"
    "assert"
    "assertnot"
    "compute"
    "set")
  "Commands producing side-effects.")

(defconst lambdapi-misc-keywords
  '("TYPE" "left" "right" "infix" "prefix"
    "protected" "private" "injective" "constant" "open" "as"))

(defvar lambdapi-indent-basic 2
  "Basic indentation for lambdapi-mode.")

(defvar lambdapi-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\/ ". 12b" table)
    (modify-syntax-entry ?\n "> b" table)
    (modify-syntax-entry ?_ "w" table)
    table)
  "Syntax table for lambdapi-mode.")

(defvar lambdapi-mode-map (make-sparse-keymap))

(defvar lambdapi-unicode-force-quail nil
  "Set to non-nil to use Quail rather that company-math for unicode.")

(provide 'lambdapi-vars)
;;; lambdapi-vars.el ends here
