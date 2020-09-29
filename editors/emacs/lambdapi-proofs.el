;;; lambdapi-proofs.el --- Proof interactivity for lambadpi-mode -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
;;; Commentary:
;;
;;
;;; Code:

(require 'highlight)

(defconst lp-goal-line-prefix "---------------------------------------------------")

(defun display-goals (goals)
  "Display GOALS returned by the LSP server in the dedicated Emacs buffer."
  (let ((goalsbuf (get-buffer-create "*Goals*")))
    (with-current-buffer goalsbuf
      (read-only-mode -1)
      (if (> (length goals) 0)
          (let* ((fstgoal  (elt goals 0))
                 (hs       (plist-get fstgoal :hyps))
                 (hypsstr  (mapcar
                            (lambda (hyp)
                              (let ((name (plist-get hyp :hname))
                                    (type (plist-get hyp :htype)))
                                (format "%s: %s\n" name type)))
                            (reverse hs)))
                 (goalsstr (mapcar
                            (lambda (goal)
                              (let ((id (plist-get goal :gid))
                                    (type (plist-get goal :type)))
                                (format "%s\nGoal %d: %s\n\n"
                                        lp-goal-line-prefix id type)))
                            goals)))
            (erase-buffer)
            (goto-char (point-max))
            (mapc 'insert hypsstr)
            (mapc 'insert goalsstr))
        (erase-buffer))
      (read-only-mode 1))))


(defun eglot--signal-proof/goals (position)
  "Send proof/goals to server, requesting the list of goals at POSITION."
  (let ((server (eglot-current-server))
        (params `(:textDocument ,(eglot--TextDocumentIdentifier)
                  :position ,position)))
    (if server
        (let ((response (jsonrpc-request server :proof/goals params)))
          (if response
              (display-goals (plist-get response :goals))
            (let ((goalsbuf (get-buffer-create "*Goals*")))
              (with-current-buffer goalsbuf
                (read-only-mode -1)
                (erase-buffer)
                (read-only-mode 1))))))))

(defun lp-display-goals ()
  "Display goals at cursor position."
  (interactive)
  (eglot--signal-proof/goals (eglot--pos-to-lsp-position)))

(defvar proof-line-position (list :line 0 :character 0))
(defvar interactive-goals 't)

(defun move-proof-line (move-fct)
  (save-excursion
    (let ((line (plist-get proof-line-position :line)))
      (setq proof-line-position
            (eglot--widening (list :line (funcall move-fct line) :character 0)))
      (goto-line line)
      (hlt-unhighlight-region 0 (1+ (line-end-position)))
      (goto-line (funcall move-fct line))
      (hlt-highlight-region 0 (1+ (line-end-position)))
      (lp-display-goals))))

(defun lp-proof-forward ()
  "Move the proof cursor forward."
  (interactive)
  (move-proof-line #'1+))

(defun lp-proof-backward ()
  "Move the proof cursor backward."
  (interactive)
  (move-proof-line #'1-))

(defun toggle-interactive-goals ()
  "Toggle the goals display between two modes: interactive and step by step."
  (interactive)
  (save-excursion
    (let ((line (plist-get proof-line-position :line)))
      (if interactive-goals
          (progn
              (setq proof-line-position
                    (eglot--widening
                     (list :line (line-number-at-pos) :character 0)))
              (goto-line (line-number-at-pos))
              (hlt-highlight-region 0 (1+ (line-end-position))))
        (goto-line line)
        (hlt-unhighlight-region 0 (1+ (line-end-position))))))
  (setq interactive-goals (not interactive-goals)))

;; Keybindings for goals display
(global-set-key (kbd "C-c C-c") 'lp-display-goals)
(global-set-key (kbd "C-c C-i") 'toggle-interactive-goals)
(global-set-key (kbd "C-c C-p") 'lp-proof-backward)
(global-set-key (kbd "C-c C-n") 'lp-proof-forward)

(provide 'lambdapi-proofs)
;;; lambdapi-proofs.el ends here
