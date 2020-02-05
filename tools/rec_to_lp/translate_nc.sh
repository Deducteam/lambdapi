#!/bin/bash
## This scripts translates all the haskell files from the HASKELL to a DEDUKTI
## directory with the dedukti(3) syntax.

src="HASKELL"
out="DEDUKTI"
mkdir -p "$out"
(cd "$src" || exit
for f in *.hs; do
  if ! grep '==\|=/=' "$f"; then
    ../rec_hs_to_lp.awk "$f" > "../${out}/${f%.hs}.lp"
  fi
done)
