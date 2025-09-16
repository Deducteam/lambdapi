#! emacs -q --script 
;;; load package module
(require 'package)
(dolist (url '(("melpa" . "https://melpa.org/packages/")
           ("melpa-stable" . "http://stable.melpa.org/packages/")
       ))
  (add-to-list 'package-archives url t))
(package-initialize)

;;; read package list from `packages` file
(defvar *packages-list '("highlight" "math-symbol-lists"))


(unless package-archive-contents
  (package-refresh-contents))

;;; install packages
(dolist (package *packages-list)
  (if (package-installed-p (intern package))
      (princ (format "%s already installed \n" package))
    (progn
      (princ (format "%s is installing \n" package))
      (package-install (intern package))
      (princ (format "%s installed \n\n")))))