#!/bin/sh
## Test the lambdapi-mode built from '*.el' files.
## The script  downloads a  fresh and basic  configuration, creates  a temporary
## directory and launches emacs in it. You  can create a new 'foo.lp' to try the
## mode.
##
## Usage: tests.sh NAME VERSION
set -eu
NAME="$1"
VERSION="$2"
tmp="$(mktemp -d)"
make dist
cp "${NAME}-${VERSION}.tar" "${tmp}"
(cd "${tmp}" || exit 1
 curl https://sanemacs.com/sanemacs.el > sanemacs.el
 {
     echo '(setq package-check-signature nil)';
     echo '(use-package eglot)';
     echo '(use-package math-symbol-lists)';
     echo '(use-package highlight)';
 } >> sanemacs.el
 emacs --quick -l sanemacs.el \
     --eval "(package-install-file \"${NAME}-${VERSION}.tar\")")
rm -rf "${tmp}"
