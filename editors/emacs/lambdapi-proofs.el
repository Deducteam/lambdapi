;;; lambdapi-proofs.el --- Proof interactivity for lambadpi-mode -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
;;; Commentary:
;;
;;
;;; Code:

(require 'highlight)
(require 'cl-lib)

(defconst lambdapi-terminators '(";" "begin")
  "List of terminators for electric terminator mode")

(defface lambdapi-proof-face
  '((((background dark)) :background "darkgreen")
    (((background light)) :background "darkseagreen2"))
  "Face for evaluated region")

(defface lambdapi-proof-error-face
  '((((background dark)) :background "brown")
    (((background light)) :background "indianred1"))
  "Face for regions with error")

(defun lp--get-first-error-before (before)
  "Returns the position of first error before BEFORE and nil if there are
no errors."
  (save-restriction
    (widen)
    (let* ((diags (flymake-diagnostics (point-min) before))
           (error-diags
            (cl-remove-if-not
             (lambda (diag)
               (eq 1 (cadr (member :severity
                                   (car (flymake-diagnostic-data diag))))))
             diags))
           (lsp-positions
            (mapcar
             (lambda (diag)
               (cadr (member :start
                             (cadr (member :range
                                           (car (flymake-diagnostic-data diag)))))))
             error-diags))
           (points
            (mapcar (lambda (lsp-pos)
                      (eglot--lsp-position-to-point lsp-pos))
                    lsp-positions))
           (first-error (1+ (point-max))))
      (mapcar (lambda (pos) (setq first-error (min first-error pos)))
              points)
      (if (> first-error (point-max)) nil first-error))))

(defun lp-highlight-till (pos)
  "Highlight till pos"
  (save-restriction
    (widen)
    (hlt-unhighlight-region (point-min) (point-max) 'lambdapi-proof-face)
    (hlt-unhighlight-region (point-min) (point-max) 'lambdapi-proof-error-face)
    (let ((first-error (lp--get-first-error-before pos)))
      (if first-error
          (progn
            (hlt-highlight-region
             (point-min) (min (1+ pos) first-error) 'lambdapi-proof-face)
            (hlt-highlight-region
             first-error (min (1+ pos) (point-max)) 'lambdapi-proof-error-face))
        (hlt-highlight-region
         (point-min) (min (1+ pos) (point-max))
         'lambdapi-proof-face)))))

(defun lp-focus-goal (goalno &optional proofbuf proofpos)
  "Focus on 'goalno'th goal (zero-indexed). proofbuf is the buffer
containing the corresponding proof for *Goals* buffer"
  (interactive "nEnter Goal Number: ")
  (if (null proofbuf)
      (setq proofbuf (plist-get proof-line-position :buffer)
            proofpos (plist-get proof-line-position :pos)))
  (select-window (get-buffer-window proofbuf))
  (with-current-buffer proofbuf
    (goto-char proofpos)
    ;; Don't focus the goalno 0
    (if (not (eq goalno 0))
        (progn
          (forward-char)
          (insert (format "\nfocus %S;" goalno))
          (smie-indent-line)
          (eglot--signal-textDocument/didChange)
          (lp-move-proof-line `(lambda (_) ,(1- (point))))))))

(defun lp-make-goal-clickable (goalstr goalNo proofbuf proofpos)
  "Returns goalstr with text properties added making the string call
lp-focus-goal with goalNo and proofbuf on click. Also makes the string
bold if goalNo is 0"
  (let ((goalkeymap (make-sparse-keymap)))
    (define-key goalkeymap [mouse-1]
      `(lambda ()
         (interactive)
         (lp-focus-goal ,goalNo ,proofbuf ,proofpos)))
    (add-text-properties
     0 (length goalstr)
     `(face
       ,(pcase goalNo
          (0 'bold)
          (_ 'default))
       mouse-face highlight
       help-echo ,(pcase goalNo
                    (0 "current goal")
                    (_ "click to focus"))
       keymap    ,goalkeymap)
     goalstr)
    goalstr))

(defun lp-format-string-hyps-goal (goal)
  "Return the string associated to the hypotheses of a single typing goal"
  (let ((tog (plist-get goal :typeofgoal)))
    (let ((hs (plist-get goal :hyps)))
      (mapcar (lambda (hyp)
                (let ((name (plist-get hyp :hname))
                      (type (plist-get hyp :htype)))
                  (format "%s: %s\n" name type)))
              hs))))

(defun lp-format-string-goal (goal goalNo proofbuf proofpos)
  "Return the string associated to a single goal. Adds text-properties to
make it clickable"
  (let ((tog (plist-get goal :typeofgoal)))
    (if (string= tog "Typ")
        (let* ((id (plist-get goal :gid))
               (type (plist-get goal :type))
               (clk-text (lp-make-goal-clickable
                          (format "%s: %s" id type)
                          goalNo proofbuf proofpos)))
          (format "%s\n\n"
                  clk-text))
      (let* ((constr (plist-get goal :constr))
             (clk-text (lp-make-goal-clickable
                        (format "%s" constr)
                        goalNo proofbuf proofpos)))
        (format "%s\n\n"
                clk-text)))))

;; taken from cus-edit.el
(defun lp--draw-horizontal-line ()
  "Draw a horizontal line at point.
This works for both graphical and text displays."
  (let ((p (point)))
    (insert "\n")
    (put-text-property p (1+ p) 'face '(:underline t))
    (overlay-put (make-overlay p (1+ p))
                 'before-string
                 (propertize "\n" 'face '(:underline t)
                             'display
                             (list 'space :align-to
                                   `(+ (0 . right)
                                       ,(min (window-hscroll)
                                             (- (line-end-position)
                                                (line-beginning-position)))))))))

(defun lp-display-goals (goals)
  "Display GOALS returned by the LSP server in the dedicated Emacs buffer."
  (let ((goalsbuf (get-buffer-create "*Goals*"))
        (proofbuf (plist-get proof-line-position :buffer))
        (proofpos (plist-get proof-line-position :pos)))
    (with-current-buffer goalsbuf
      (read-only-mode -1)
      (if (> (length goals) 0)
          (let* ((fstgoal (elt goals 0))
                 (hypsstr (lp-format-string-hyps-goal fstgoal))
                 ;; map each goal to formatted goal string
                 (goalsstr (cl-mapcar
                            `(lambda (goal goalNo)
                               (lp-format-string-goal
                                goal goalNo ,proofbuf ,proofpos))
                            goals
                            (cl-loop for x below (length goals)
                                     collect x))))
            (remove-overlays)
            (erase-buffer)
            (goto-char (point-max))
            (mapc 'insert hypsstr)
            (mapc (lambda (gstr)
                    (lp--draw-horizontal-line)
                    (insert gstr))
                  goalsstr))
        (remove-overlays)
        (erase-buffer)
        (insert "No goals"))
      (read-only-mode 1))))

(defun lp-display-logs (logs)
  "Display logs in *lp-logs* buffer"
  (let ((logbuf (get-buffer-create "*lp-logs*")))
    (setq logs (replace-regexp-in-string
                "^[ \t\n\r]*\\(\\(\u001b\\[[0-9]+m\\)*\\)[ \t\n\r]*" "\\1"
                logs))
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
          (ansi-color-apply-on-region (point-min) (point-max)))
        ;;; remove whitespace at end of buffer
        (goto-char (point-max))
        (while (member (char-before) '(?  ?\C-j ?\C-i))
          (delete-backward-char 1))))
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
                (lp-display-goals (plist-get response :goals))
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

(defvar-local proof-line-position (list :pos 0 :buffer nil))
(defvar-local electric-terminator nil)

(defun lp-move-proof-line (move-fct)
  (let* ((pos (plist-get proof-line-position :pos))
         (npos (funcall move-fct pos)))
    (setq proof-line-position
          (list :pos npos :buffer (current-buffer)))
    (lp-prove-till npos)))

(defun lp-get-next-proof-pos (pos)
  "returns position of next proof"
  (save-excursion
    (goto-char pos)
    (if (search-forward "begin" nil t)
        (1- (point))
      (point-max))))

(defun lp-get-prev-proof-pos (pos)
  "returns position of previous proof"
  (save-excursion
    (goto-char pos)
    (if (search-backward "begin" nil t)
        (+ (length "begin") (point) -1)
      0)))

(defun lp-jump-proof-forward ()
  "Move the proof cursor to the next proof"
  (interactive)
  (lp-move-proof-line #'lp-get-next-proof-pos)
  (recenter))

(defun lp-jump-proof-backward ()
  "Move the proof cursor to the previous proof"
  (interactive)
  (lp-move-proof-line #'lp-get-prev-proof-pos)
  (recenter))

(defun lp-proof-forward ()
  "Move the proof cursor forward."
  (interactive)
  (lp-move-proof-line #'lp--next-command-pos)
  (recenter))

(defun lp-proof-backward ()
  "Move the proof cursor backward."
  (interactive)
  (lp-move-proof-line #'lp--prev-command-pos)
  (recenter))

(defun lp-prove-till-cursor ()
  "Proves till the command/tactic at cursor"
  (interactive)
  (save-excursion
    (if (and (not (lp--in-comment-p))
             (save-excursion (beginning-of-line)
                             (looking-at-p "^[[:space:]]*$")))
        (progn
          (end-of-line)
          (lp-prove-till (point)))
      (if (string-match "[\n\t ]" (string (char-before (point))))
          (re-search-forward "[^\n\t ]"))
      (if (save-excursion
            (skip-syntax-forward ".")
            (lp--in-comment-p))
          (progn
            (skip-syntax-forward ".")
            (let ((comment-type (nth 7 (syntax-ppss))))
              (goto-char (nth 8 (syntax-ppss)))
              (forward-comment 1)
              (skip-syntax-backward "> ")
              (lp-prove-till (1- (point)))))
        (let ((line-empty ; line empty or is a single line comment
               (save-excursion
                 (beginning-of-line)
                 (looking-at-p "\\([[:space:]]*\\|//.*\\)$"))))
          (lp-prove-till
           (if line-empty
               (lp--prev-command-pos (1+ (point)))
             (lp--next-command-pos (1- (point))))))))))

(defun lp-prove-till (pos)
  "Evaluates till pos and moves the cursor to the end of evaluated region"
  (lp-highlight-till pos)
  (setq proof-line-position
        (list :pos pos :buffer (current-buffer)))
  (goto-char pos)
  (eglot--signal-proof/goals (eglot--pos-to-lsp-position)))

(defun lp-toggle-electric-terminator ()
  "Toggle the between two modes: electric terminator and step by step."
  (interactive)
  (setq electric-terminator (not electric-terminator))
  (save-excursion
    (if electric-terminator
        (let ((prev-cmd-pos (lp--prev-command-pos)))
          (lp-prove-till prev-cmd-pos))
      (hlt-unhighlight-region 0 (point-max))))
  ;; update the tool-bar icon
  (define-key lambdapi-mode-map [tool-bar lp-toggle-electric-terminator]
    `(menu-item "Electric" lp-toggle-electric-terminator
                :image
                (image :type xpm :file ,(if electric-terminator
                                            "connect.xpm" "disconnect.xpm"))
                :help "Toggle electric terminator"))
  (force-mode-line-update)
  (message (format "Electric terminator is %s"
                   (if electric-terminator "ON" "OFF"))))

(defun lp--in-comment-p (&optional pos)
  "Returns t if character at pos is in a comment.
If pos is nil use (point)"
  (unless pos (setq pos (point)))
  (nth 4 (syntax-ppss)))

(defun lp--prev-command-pos (&optional pos)
  "Returns the position of the previous command's terminator
and 0 if there is no previous command"
  (unless pos (setq pos (point)))
  (save-excursion
    (let ((term-regex
           (mapconcat
            (lambda (s) (format "\\(%s\\)" s))
            lambdapi-terminators "\\|")))
      (goto-char pos)
      (while
          (progn
            (setq pos (re-search-backward term-regex nil t))
            (and pos (lp--in-comment-p pos)))
        (goto-char pos))
      (if pos
          (let ((match-len ; length of matched terminator
                 (seq-some
                  (lambda (term)
                    (if (looking-at-p term)
                        (length term)
                      nil))
                  lambdapi-terminators)))
            (1- (+ pos match-len)))
        0))))

(defun lp--next-command-pos (&optional pos)
  "Returns the position of the next command's terminator
and pos if there is no next command"
  (setq npos (1+ (or pos (point))))
  (save-excursion
    (let ((term-regex
           (mapconcat
            (lambda (s) (format "\\(%s\\)" s))
            lambdapi-terminators "\\|")))
      (goto-char npos)
      (while
          (progn
            (setq npos (re-search-forward term-regex nil t))
            (and npos (lp--in-comment-p npos)))
        (goto-char npos))
      (if npos (max (point-min) (1- npos)) pos))))

(defun lp--post-self-insert-function ()
  (save-excursion
    (if electric-terminator
        (if (and (not (lp--in-comment-p))
                 (seq-find
                  (lambda (term)
                    (equal (buffer-substring-no-properties
                            (max (point-min) (- (point) (length term)))
                            (point))
                           term))
                  lambdapi-terminators))
            (progn
              (eglot--signal-textDocument/didChange)
              (lp-prove-till (point)))))))

(defun lp--after-change-function (beg end len)
  (if (<= beg (plist-get proof-line-position :pos))
      (save-excursion
        (eglot--signal-textDocument/didChange)
        (lp-prove-till
         (lp--prev-command-pos beg)))))

(provide 'lambdapi-proofs)
;;; lambdapi-proofs.el ends here
