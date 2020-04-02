#!/bin/bash

## Open a minimal emacs with lambdapi mode
## First argument is the version

confurl='https://sanemacs.com/sanemacs.el'
conf='init.el'
curl "$confurl" > "${conf}"
(cd .. || exit
 make dist
 emacs --quick -l "tests/${conf}" \
     --eval "(package-install-file \"lambdapi-mode-${1}.tar\")"
)
