;;; lambdapi-capf.el --- Completion for lambdapi -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CECILL-2.1
;;; Commentary:
;;
;; If (add-to-list 'eglot-stay-out-of 'company) is not called, Eglot
;; reinitialises company-backends.
;;
;;; Code:
(require 'lambdapi-vars)
(require 'eglot)

;; Silence warnings
(defvar company-backends nil)
(declare-function company-math-symbols-unicode "ext:company-math.el" t t)

(defconst lambdapi--all-keywords
  (append lambdapi-sig-commands
          lambdapi-tactics
          lambdapi-misc-commands
          lambdapi-misc-keywords)
  "All keywords to complete.")

(defun lambdapi--static-completion (words)
  "Return list of completion-at-point's elements using WORDS as candidates."
  (when (or this-command (thing-at-point 'symbol))
    (let* ((bounds (bounds-of-thing-at-point 'symbol))
           (beg (or (car bounds) (point)))
           (end (or (cdr bounds) (point))))
      (list beg end words :exclusive 'no))))

(defun lambdapi--company-setup ()
  "Setup company for lambdapi."
  (when (require 'company-math nil 1) ; load company-math if available
    (add-to-list 'eglot-stay-out-of 'company) ; Eglot reinits backends
    (setq-local company-backends
                (cons #'company-math-symbols-unicode company-backends))))

;;;###autoload
(defun lambdapi-completion-at-point ()
  "Completion of symbol at point for lambdapi."
  (lambdapi--static-completion lambdapi--all-keywords))

(defun lambdapi-capf-setup ()
  "Setup for `completion-at-point-functions`."
  (let ((capf #'lambdapi-completion-at-point))
    (unless (memq capf completion-at-point-functions)
      (add-hook 'completion-at-point-functions capf nil 'local))
    (lambdapi--company-setup)))


(provide 'lambdapi-capf)
;;; lambdapi-capf.el ends here
