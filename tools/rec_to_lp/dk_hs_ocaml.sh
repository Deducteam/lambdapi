#!/bin/bash
## Compare timing of tests files between Haskell, OCaml and Dedukti3
set -eu -o pipefail
shopt -s failglob

export TIMEFORMAT="%E" # Only seconds
dksrc='DEDUKTI'
mlsrc='OCAML'
hssrc='HASKELL'

if [[ ! -f "$mlsrc" ]]; then
 svn co 'https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/OCAML'
fi
for lpf in "${dksrc}"/*; do
  root="$(basename "${lpf%.lp}")"
  t_lp="$(time (lambdapi "${dksrc}/${root}.lp" &> /dev/null))"
  t_ghcrun="$(time (runghc "${hssrc}/${root}.hs" &> /dev/null))"
  t_ocaml="$(time (ocaml "${mlsrc}/${root}.ml" &> /dev/null))"
  # For ghc and ocamlopt, we time compilation and execution
  t_ghc="$(time (cd "${hssrc}" || exit && ghc "${root}.hs" && \
         "./${root}" &> /dev/null))"
  t_mlopt="$(time (cd "${mlsrc}" || exit && ocamlopt "${root}.ml" && \
          ./a.out &> /dev/null))"
  echo -e "${root}: ${t_lp}/${t_ghcrun}/${t_ocaml}/${t_ghc}/${t_mlopt}"
done
