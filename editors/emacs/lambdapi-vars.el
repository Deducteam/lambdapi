;;; lambdapi-vars.el --- Variables for lambadpi-mode -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CECILL-2.1
;;; Commentary:
;;
;; The lists defined are mainly used for syntax colouring and completion.
;;
;;; Code:

(defconst lambdapi-tactics
  '("apply"
    "assume"
    "change"
    "generalize"
    "have"
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

(defconst lambdapi-sig-commands
  '("as"
    "begin"
    "builtin"
    "coerce_rule"
    "end"
    "eval"
    "in"
    "inductive"
    "let"
    "notation"
    "open"
    "require"
    "rule"
    "symbol"
    "unif_rule"
    "with")
  "Commands that enrich the signature.")

(defconst lambdapi-warning
  '("abort"
    "admit"
    "admitted"
    "fail")
  "To be displayed in red.")

(defconst lambdapi-misc-commands
  '("assert"
    "assertnot"
    "compute"
    "debug"
    "flag"
    "off"
    "on"
    "print"
    "proofterm"
    "prover"
    "prover_timeout"
    "search"
    "type"
    "verbose")
  "Commands not affecting the signature.")

(defconst lambdapi-misc-keywords
  '("associative"
    "commutative"
    "constant"
    "left"
    "right"
    "infix"
    "injective"
    "opaque"
    "postfix"
    "prefix"
    "private"
    "protected"
    "quantifier"
    "sequential"
    "TYPE"))

(defcustom lambdapi-indent-basic 2
  "Basic indentation for lambdapi-mode."
  :type 'number
  :options '(2 4)
  :group 'lambdapi)

(defvar lambdapi-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\/ ". 124" table)
    (modify-syntax-entry ?* ". 23b" table)
    (modify-syntax-entry ?Π "." table)
    (modify-syntax-entry ?λ "." table)
    (modify-syntax-entry ?→ "." table)
    (modify-syntax-entry ?↪ "." table)
    (modify-syntax-entry ?≔ "." table)
    (modify-syntax-entry ?$ "." table)
    (modify-syntax-entry ?? "." table)
    (modify-syntax-entry ?: "." table)
    (modify-syntax-entry ?, "." table)
    (modify-syntax-entry ?\n "> " table)
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
