#!/bin/bash

## Open a minimal emacs with lambdapi mode
## First argument is the version

conf='https://sanemacs.com/sanemacs.el'
curl "$conf" > 'emacs.el'
(cd .. || exit
 make dist
 emacs --no-site-file -q -l 'tests/emacs.el' \
     --eval "(package-install-file \"lambdapi-mode-${1}.tar\")"
)
