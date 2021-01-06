;;; lambdapi-vars.el --- Variables for lambadpi-mode -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
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
    "solve"
    "symmetry"
    "why3")
  "Proof tactics.")

(defconst lambdapi-sig-commands
  '("as"
    "in"
    "let"
    "declared"
    "builtin"
    "open"
    "begin"
    "end"
    "require"
    "rule"
    "symbol"
    "inductive"
    "with")
  "Commands that enrich the signature.")

(defconst lambdapi-warning
  '("abort" "admit" "fail")
  "To be displayed in red.")

(defconst lambdapi-misc-commands
  '("type"
    "assert"
    "assertnot"
    "compute"
    "set")
  "Commands producing side-effects.")

(defconst lambdapi-misc-keywords
  '("TYPE" "left" "right" "infix" "prefix" "quantifier"
    "protected" "private" "injective" "constant" "opaque"))

(defcustom lambdapi-indent-basic 2
  "Basic indentation for lambdapi-mode."
  :type 'number
  :options '(2 4)
  :group 'lambdapi)

(defvar lambdapi-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\/ ". 12b" table)
    (modify-syntax-entry ?Π "." table)
    (modify-syntax-entry ?λ "." table)
    (modify-syntax-entry ?→ "." table)
    (modify-syntax-entry ?↪ "." table)
    (modify-syntax-entry ?≔ "." table)
    (modify-syntax-entry ?$ "." table)
    (modify-syntax-entry ?? "." table)
    (modify-syntax-entry ?: "." table)
    (modify-syntax-entry ?, "." table)
    ;; (modify-syntax-entry ?| "\\" table) ; | instead of {| |} for simplicity
    (modify-syntax-entry ?\n "> b" table)
    (modify-syntax-entry ?. "w" table)
    (modify-syntax-entry ?_ "w" table)
    table)
  "Syntax table for lambdapi-mode.")

(defvar lambdapi-mode-map (make-sparse-keymap))

(defvar lambdapi-unicode-prefer-company nil
  "Set to non-nil to favour company-math over quail.
Useful for people who prefer to have the dropdown window display systematically,
since the window won't display if there are quail candidates.")

(provide 'lambdapi-vars)
;;; lambdapi-vars.el ends here
