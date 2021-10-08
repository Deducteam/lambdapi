;; SPDX-License-Identifier: CECILL-2.1
(defconst lambdapi--temp-buffer-name "lp-asdf2io3jnc"  ; any random name will work
  "Buffer name for used by `lambdapi-refresh-window-layout'. Must
not match any buffer used by user")

(defun lambdapi--apply-window-layout (tree)
  "Applies the window configuration given by the argument tree,
it is either a list (split-side ratio child1-tree child2-tree)
or a leaf which is a buffer or a string with buffer's name.

It is meant to be called by `lambdapi-refresh-window-layout'
which also replaces buffers with name `lambdapi--temp-buffer-name'
with the current buffer.

Example:

(lambdapi--apply-window-layout
               '(h 0.6 \"proofs\" (v 0.3 \"goals\" \"logs\")))

will produce

+------------+--------+
|            | goals  |
|   proofs   +--------+
|            | logs   |
|            |        |
+------------+--------+
"
  (if (not (listp tree))
      (switch-to-buffer (eval tree) t t)
    (let* ((way   (car tree))
           (ratio  (eval (cadr tree)))
           (child1 (caddr tree))
           (child2 (cadddr tree))
           curwin sibling)
      (if (eq way 'h)
          (progn
            (split-window-horizontally
             (truncate (* ratio (window-width))))
            (setq curwin  (selected-window))
            (setq sibling (next-window)))
        (progn
          (split-window-vertically
           (truncate (* ratio (window-height))))
          (setq curwin  (selected-window))
          (setq sibling (next-window))))
      (with-selected-window curwin
        (lambdapi--apply-window-layout child1))
      (with-selected-window sibling
        (lambdapi--apply-window-layout child2)))))

(defun lambdapi-refresh-window-layout ()
  "Resets the window layout to default."
  (interactive)
  (let ((curbuf (current-buffer)))
    (delete-other-windows)
    (lambdapi--apply-window-layout lambdapi-window-layout)
    (dolist (win (get-buffer-window-list lambdapi--temp-buffer-name))
      (with-selected-window win
        (switch-to-buffer curbuf t t)))
    (kill-buffer lambdapi--temp-buffer-name)
    (select-window (get-buffer-window curbuf))))

(defcustom lambdapi-window-X-ratio 0.5
  "Ratio of height taken in horizontal split during window layout.
(Not applicable to Layout 0)"
  :type '(float)
  :group 'lambdapi)

(defcustom lambdapi-window-Y-ratio 0.8
  "Ratio of width taken in vertical split during window layout
(Not applicable to Layout 0)"
  :type '(float)
  :group 'lambdapi)

(defcustom lambdapi-window-layout '(v 0.35
                                      lambdapi--temp-buffer-name
                                      (v 0.35 "*Goals*" "*lp-logs*"))
  "Window layout of LambdaPi."
  :group 'lambdapi
  ;; :set might change window layout at an unexpected time
  :set (lambda (option newval)
         (setq lambdapi-window-layout newval)
         (lambdapi-refresh-window-layout))
  :type '(radio (sexp :tag "Layout 0"
		      :format "%t\n"
		      :value
		      (v 0.75
                         lambdapi--temp-buffer-name
                         (v 0.8 "*Goals*" "*lp-logs*")))
	        (sexp :tag "Layout 1"
                      :format "%t\n"
                      :value
                      (v lambdapi-window-Y-ratio
                         lambdapi--temp-buffer-name
                         (h lambdapi-window-X-ratio
			    "*Goals*" "*lp-logs*")))
                (sexp :tag "Layout 2"
                      :format "%t\n"
                      :value
                      (v lambdapi-window-Y-ratio
                         (h lambdapi-window-X-ratio
                            lambdapi--temp-buffer-name
                            "*lp-logs*")
                         "*Goals*"))
                (sexp :tag "Layout 3"
                      :format "%t\n"
                      :value
                      (h lambdapi-window-X-ratio
                         lambdapi--temp-buffer-name
                         (v lambdapi-window-Y-ratio
                            "*lp-logs*"
                            "*Goals*")))
                (sexp :tag "Layout 4"
                      :format "%t\n"
                      :value
                      (h lambdapi-window-X-ratio
                         (v lambdapi-window-Y-ratio
                            lambdapi--temp-buffer-name
                            "*Goals*")
                         "*lp-logs*"))
                (sexp :tag "Goal bottom"
                      :format "%t\n"
                      :value
                      (v lambdapi-window-Y-ratio
                         lambdapi--temp-buffer-name
                         "*Goals*"))
                (sexp :tag "Goal right"
                      :format "%t\n"
                      :value
                      (h lambdapi-window-X-ratio
                         lambdapi--temp-buffer-name
                         "*Goals*"))))


(provide 'lambdapi-layout)
