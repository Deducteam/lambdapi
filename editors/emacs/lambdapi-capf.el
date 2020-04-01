;;; lambdapi-capf.el --- Completion for lambdapi -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Deducteam
;;
;; Author: Gabriel Hondet
;; Maintainer: Deducteam <dedukti-dev@inria.fr>
;; Created: March 28, 2020
;; Modified: March 28, 2020
;; Version: 0.0.1
;; Package-Requires: ((emacs 26.1) (cl-lib "0.5"))
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;;; Code:
(require 'lambdapi-vars)

(defconst lambdapi--all-keywords
  (append lambdapi-sig-commands
          lambdapi-tactics
          lambdapi-misc-commands
          lambdapi-misc-keywords
          lambdapi-modifiers)
  "All keywords to complete.")

(defun lambdapi--static-completion (words)
  "Return list of completion-at-point's elements using WORDS as candidates."
  (when (or this-command (thing-at-point 'symbol))
    (let* ((bounds (bounds-of-thing-at-point 'symbol))
           (beg (or (car bounds) (point)))
           (end (or (cdr bounds) (point))))
      (list beg end words :exclusive 'no))))

;;;###autoload
(defun lambdapi-completion-at-point ()
  "Completion of symbol at point for lambdapi."
  (lambdapi--static-completion lambdapi--all-keywords))

(defun lambdapi-capf-setup ()
  "Setup for `completion-at-point-functions`."
  (let ((capf #'lambdapi-completion-at-point))
    (unless (memq capf completion-at-point-functions)
      (add-hook 'completion-at-point-functions capf nil 'local))))


(provide 'lambdapi-capf)
;;; lambdapi-capf.el ends here
