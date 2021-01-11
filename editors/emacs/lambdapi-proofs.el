;;; lambdapi-proofs.el --- Proof interactivity for lambadpi-mode -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
;;; Commentary:
;;
;;
;;; Code:

(require 'highlight)
(require 'cl-lib)

(defconst lp-goal-line-prefix "---------------------------------------------------")

(defun lp-focus-goal (goalno &optional proofbuf lineNo)
  "Focus on 'goalno'th goal (zero-indexed). proofbuf is the buffer
containing the corresponding proof for *Goals* buffer"
  (interactive "nEnter Goal Number: ")
  (if (null proofbuf)
      (setq proofbuf (current-buffer)))
  (select-window (get-buffer-window proofbuf))
  (with-current-buffer proofbuf
    (goto-line (or lineNo (plist-get proof-line-position :line)))
    (goto-char (line-end-position))
    ;; Don't focus the goalno 0
    (if (not (eq goalno 0))
        (progn
          (newline)
          (insert (format "focus %S" goalno))
          (smie-indent-line)
          (eglot--signal-textDocument/didChange)
          ;; if interactive mode is on move the proofline
          ;; to the newly inserting focus k
          (if interactive-goals
              (move-proof-line `(lambda (_) ,(1+  lineNo)))
            (progn
              ;; otherwise just update the goals
              ;; we need to call interactively because we
              ;; need its behaviour similar to C-c C-c by user i.e.
              ;; to display goals without changing proof-line-position
              (call-interactively #'lp-display-goals)))))))

(defun lp-make-goal-clickable (goalstr goalNo proofbuf lineNo)
  "Returns goalstr with text properties added making the string call
lp-focus-goal with goalNo and proofbuf on click. Also makes the string
bold if goalNo is 0"
  (let ((goalkeymap (make-sparse-keymap)))
    (define-key goalkeymap [mouse-1]
      `(lambda ()
         (interactive)
         (lp-focus-goal ,goalNo ,proofbuf ,lineNo)))
    (add-text-properties
     0 (length goalstr)
     `(face      ,(pcase goalNo
                    (0 'bold)
                    (_ 'default))
       mouse-face highlight
       help-echo ,(pcase goalNo
                    (0 "current goal")
                    (_ "click to focus"))
       keymap    ,goalkeymap)
     goalstr)
    goalstr))

(defun lp-format-string-hyps-typ-goal (goal)
  "Return the string associated to the hypotheses of a single typing goal"
  (let ((tog (plist-get goal :typeofgoal)))
    (if (string= tog "Typ ")
	(let ((hs (plist-get goal :hyps)))
	  (mapcar (lambda (hyp)
		    (let ((name (plist-get hyp :hname))
			  (type (plist-get hyp :htype)))
		      (format "%s: %s\n" name type)))
		  (reverse hs))))))


(defun lp-format-string-goal (goal goalNo proofbuf proofline)
  "Return the string associated to a single goal. Adds text-properties to
make it clickable"
  (let ((tog (plist-get goal :typeofgoal)))
    (if (string= tog "Typ ")
	(let* ((id (plist-get goal :gid))
               (type (plist-get goal :type))
               (clk-text (lp-make-goal-clickable
                          (format "%s  %d: %s"
                                  tog id type)
                          goalNo proofbuf proofline)))
	  (format "%s\n%s\n\n"
		  lp-goal-line-prefix clk-text))
      (let* ((constr (plist-get goal :constr))
             (clk-text (lp-make-goal-clickable
                        (format "%s    : %s"
                                tog constr)
                        goalNo proofbuf proofline)))
        (format "%s\n%s\n\n"
                lp-goal-line-prefix clk-text)))))

(defun display-goals (goals)
  "Display GOALS returned by the LSP server in the dedicated Emacs buffer."
  (let ((goalsbuf   (get-buffer-create "*Goals*"))
        (proofbuf   (plist-get proof-line-position :buffer))
        (proofline  (plist-get proof-line-position :line)))
        (with-current-buffer goalsbuf
          (read-only-mode -1)
          (if (> (length goals) 0)
              (let* ((fstgoal (elt goals 0))
                     (hypsstr (lp-format-string-hyps-typ-goal fstgoal))
                     ;; map each goal to formatted goal string
                     (goalsstr (cl-mapcar `(lambda (goal goalNo)
                                             (lp-format-string-goal
                                              goal goalNo ,proofbuf ,proofline))
                                          goals
                                          (cl-loop for x below (length goals)
                                                   collect x))))
                (erase-buffer)
                (goto-char (point-max))
                (mapc 'insert hypsstr)
                (mapc 'insert goalsstr))
            (erase-buffer))
          (read-only-mode 1))))

(defun lp-display-logs (logs)
  "Display logs in *lp-logs* buffer"
  (let ((logbuf (get-buffer-create "*lp-logs*")))
    (with-current-buffer logbuf
      (read-only-mode +1)
      (with-silent-modifications
        (set (make-local-variable 'window-point-insertion-type) t)
	(erase-buffer)
	(insert logs)
        ;; TODO: fix performance issue
        ;; See: https://emacs.stackexchange.com/a/38608/30239
        (let ((ansi-color-apply-face-function
               (lambda (beg end face)
                 (when face
                   (put-text-property beg end 'face face)))))
          (ansi-color-apply-on-region (point-min) (point-max)))))
    (let ((logwin (get-buffer-window logbuf)))
      (if logwin
          (with-selected-window logwin
            (goto-char (point-max))
            (beginning-of-line)
            (recenter -1))))))


(defun eglot--signal-proof/goals (position)
  "Send proof/goals to server, requesting the list of goals at POSITION."
  (let ((server (eglot-current-server))
        (params `(:textDocument ,(eglot--TextDocumentIdentifier)
                  :position ,position)))
    (if server
        (let ((response (jsonrpc-request server :proof/goals params)))
          (if response
              (progn
		(display-goals (plist-get response :goals))
		(lp-display-logs (plist-get response :logs)))
            (let ((goalsbuf (get-buffer-create "*Goals*"))
                  (logsbuf (get-buffer-create "*lp-logs*")))
              (with-current-buffer goalsbuf
                (read-only-mode -1)
                (erase-buffer)
                (read-only-mode 1))
              (with-current-buffer logsbuf
                (read-only-mode -1)
                (erase-buffer)
                (read-only-mode 1))))))))

(defun lp-display-goals ()
  "Display goals at cursor position."
  (interactive)
  (if (called-interactively-p 'any)
      (let ((temp-pfline proof-line-position))
        (setq proof-line-position (list :line (1+ (current-line)) :character 0
                                        :buffer (current-buffer)))
        (eglot--signal-proof/goals (eglot--pos-to-lsp-position))
        (setq proof-line-position temp-pfline))
    (eglot--signal-proof/goals (eglot--pos-to-lsp-position))))

(defvar-local proof-line-position (list :line 0 :character 0 :buffer nil))
(defvar-local interactive-goals nil)

(defun move-proof-line (move-fct)
  (save-excursion
    (let ((line (plist-get proof-line-position :line)))
      (setq proof-line-position
            (eglot--widening (list :line (funcall move-fct line) :character 0
                                   :buffer (current-buffer))))
      (goto-line line)
      (hlt-unhighlight-region 0 (point-max))
      (goto-line (funcall move-fct line))
      (hlt-highlight-region 0 (1+ (line-end-position)))
      (lp-display-goals))))

(defun lp-get-next-proof-line (lineNo)
  "returns line number of next proof"
  (save-excursion
    (goto-line (1+ lineNo))
    (if (not (search-forward "begin" nil t))
	(goto-char (point-max)))
    (line-number-at-pos)))

(defun lp-get-prev-proof-line (lineNo)
  "returns line number of previous proof"
  (save-excursion
    (goto-line lineNo)
    (if (not (search-backward "begin" nil t))
	(goto-char (point-min)))
    (line-number-at-pos)))

(defun lp-jump-proof-forward ()
  "Move the proof cursor to the next proof"
  (interactive)
  (move-proof-line #'lp-get-next-proof-line))

(defun lp-jump-proof-backward ()
  "Move the proof cursor to the previous proof"
  (interactive)
  (move-proof-line #'lp-get-prev-proof-line))

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
  (setq interactive-goals (not interactive-goals))
  (save-excursion
    (let ((line (plist-get proof-line-position :line)))
      (if interactive-goals
          (progn
              (setq proof-line-position
                    (eglot--widening
                     (list :line (line-number-at-pos) :character 0)))
              (goto-line (line-number-at-pos))
              (hlt-highlight-region 0 (1+ (line-end-position)))
              (lp-display-goals))
        (goto-line line)
        (hlt-unhighlight-region 0 (point-max)))))
  (message (format "Interactive mode is %s"
                   (if interactive-goals "ON" "OFF"))))

(provide 'lambdapi-proofs)
;;; lambdapi-proofs.el ends here
