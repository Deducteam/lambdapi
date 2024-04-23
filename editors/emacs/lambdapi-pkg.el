;;; lambdapi-pkg.el --- A major mode to edit Lambdapi files -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2024 Gabriel Hondet
;;
;; Authors: Ashish Barnawal, Diego Riviero, Gabriel Hondet, Rodolphe Lepigre
;; Maintainer: Deducteam <dedukti-dev@inria.fr>
;; Created: April 23, 2024
;; Modified: April 23, 2024
;; Version: 1.1.0
;; Keywords: languages
;; SPDX-License-Identifier: CECILL-2.1
;; Homepage: https://github.com/Deducteam/lambdapi
;; Package-Requires: ((emacs "26.1") (eglot "1.8") (math-symbol-lists "1.2.1") (highlight "20190710.1527"))
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;; A major mode for the Lambdapi proof assistant.
;;
;;; Code:

(define-package "lambdapi" "1.1.0"
  "A major mode to edit Lambdapi files."
  '((eglot "1.8")
    (math-symbol-lists "1.2.1")
    (highlight "20190710.1527")))

(provide 'lambdapi-pkg)
;;; lambdapi-pkg.el ends here
