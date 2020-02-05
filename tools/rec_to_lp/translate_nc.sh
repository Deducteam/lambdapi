#!/bin/bash
## This scripts translates all the haskell files from the HASKELL to a DEDUKTI
## directory with the dedukti(3) syntax.
## NOTE tests using conditional rewriting are not translated

set -eu -o pipefail
shopt -s failglob

src="HASKELL"
out="DEDUKTI"
if [[ ! -f HASKELL ]]; then
  svn co 'https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/HASKELL'
fi
mkdir -p "$out"
(cd "$src" || exit
for f in *.hs; do
  if ! grep '==\|=/=' "$f"; then # skip conditional rewriting
    ../rec_hs_to_lp.awk "$f" > "../${out}/${f%.hs}.lp"
  fi
done)
