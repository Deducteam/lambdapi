#!/bin/bash
## Compare timing of tests files between Haskell, OCaml and Dedukti3
set -euf -o pipefail

export TIMEFORMAT="%E" # Only seconds
dksrc='DEDUKTI'
mlsrc='OCAML'
hssrc='HASKELL'

files="(cd "${dksrc}" || exit && ls)"

if [[ ! -f "$mlsrc" ]]; then
 svn co 'https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/OCAML'
fi
for lpf in files; do
  root=${lpf%.lp}
  t_lp="$(time lambdapi --verbose 0 "${dksrc}/${lpf}")"
  t_ghcrun="$(time ghcrun "${hssrc}/${root}.hs")"
  t_ocaml="$(time ocaml "${mlsrc}/${root}.ml")"
  # For ghc and ocamlopt, we time compilation and execution
  t_ghc="$(time (cd "${hssrc}" || exit && ghc "${root}.hs" && ./${root}))"
  t_mlopt="$(time (cd "${mlsrc}" || exit && ocamlopt "${root}.ml" && \
          ./a.out))"
  echo -e "${root}: ${t_lp}/${t_ghcrune}/${t_ocaml}/${t_ghc}/${t_mlopt}"
done
