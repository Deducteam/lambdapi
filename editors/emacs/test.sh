#!/bin/sh
## Test the lambdapi-mode built from '*.el' files.
## The script  downloads a  fresh and basic  configuration, creates  a temporary
## directory and launches emacs in it. You  can create a new 'foo.lp' to try the
## mode.
##
## Takes the version of the mode as first argument
set -eu
tmp="$(mktemp -d)"
make dist
cp "lambdapi-$1.tar" "${tmp}"
(cd "${tmp}" || exit 1
 curl https://sanemacs.com/sanemacs.el > sanemacs.el
 {
     echo '(setq package-check-signature nil)';
     echo '(use-package eglot)';
     echo '(use-package math-symbol-lists)';
     echo '(use-package highlight)';
 } >> sanemacs.el
 emacs --quick -l sanemacs.el \
     --eval "(package-install-file \"lambdapi-$1.tar\")")
rm -rf "${tmp}"
