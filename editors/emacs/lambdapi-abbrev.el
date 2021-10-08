;;; lambdapi-abbrev.el --- Abbrevs for lambdapi -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CECILL-2.1
;;; Commentary:
;;
;;  Abbreviations can be used to enter UTF-8 characters.
;;
;;; Code:
(require 'lambdapi-vars)
(defun lambdapi-local-abbrev (expansion)
  "Add abbreviation expanding word at point to EXPANSION.
The abbreviation is added into the `local-abbrev-table', so it is available in
all `lambdapi-mode' buffers. The `local-abbrev-table' is rewritten to directory
local variables at each new definition."
  (interactive "sExpands to:")
  (let ((bufname (buffer-name))
        (name (buffer-substring-no-properties
               (point)
               (save-excursion (forward-word (- 1)) (point)))))
    (define-abbrev local-abbrev-table name expansion nil :system t)
    (add-dir-local-variable
     'lambdapi-mode 'eval
     `(define-abbrev local-abbrev-table ,name ,expansion nil :system t))
    (save-buffer)
    (switch-to-buffer bufname)))

(defun lambdapi-abbrev-setup ()
  "Set up lambdapi abbreviation."
  (abbrev-mode 1)
  (define-key lambdapi-mode-map (kbd "C-c C-a") #'lambdapi-local-abbrev))

(provide 'lambdapi-abbrev)
;;; lambdapi-abbrev.el ends here
