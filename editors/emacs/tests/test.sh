#!/bin/bash
# TODO: add switch to test or not company

set -euf -o pipefail
## Open a minimal emacs with lambdapi mode
## First argument is the version

elpa='https://elpa.gnu.org/packages'
confurl='https://sanemacs.com/sanemacs.el'
conf='init.el'
curl "$confurl" > "${conf}"
# Add elpa repo
sed -i "/(add-to-list 'package-archives.*)$/a \
(add-to-list 'package-archives '(\"gnu\" . \"${elpa}\"))\\n" \
"$conf"
# Add company installation
{ printf "(use-package company :pin gnu)\\n" ;
  printf "(use-package company-math :pin gnu)\\n" ;
  printf "(global-company-mode)\\n"; } >> "${conf}"
(cd .. || exit
 make dist
 emacs --quick -l "tests/${conf}" \
     --eval "(package-install-file \"lambdapi-mode-${1}.tar\")"
)
