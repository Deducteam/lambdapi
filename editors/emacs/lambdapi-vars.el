;;; lambdapi-vars.el --- Variables for lambadpi-mode -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Deducteam
;;
;; Maintainer: Deducteam <dedukti-dev@inria.fr>
;; Created: March 28, 2020
;; Modified: March 28, 2020
;; Package-Requires: ((emacs 26.1) (cl-lib "0.5"))
;;
;; This file is not part of GNU Emacs.
;;
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
    "symmetry"
    "why3")
  "Proof tactics.")

(defconst lambdapi-sig-commands
  '("abort"
    "admit"
    "and"
    "definition"
    "let"
    "proof"
    "qed"
    "require"
    "rule"
    "symbol"
    "theorem")
  "Commands that enrich the signature.")

(defconst lambdapi-misc-commands
  '("type"
    "assert"
    "assertnot"
    "compute"
    "set")
  "Commands producing side-effects.")

(defconst lambdapi-misc-keywords
  '("TYPE" "left" "right" "infix" "prefix"))

(defconst lambdapi-modifiers
  '("protected" "private" "injective" "constant" "open" "as")
  "Symbol modifiers.")

(provide 'lambdapi-vars)
;;; lambdapi-vars.el ends here
