#!/bin/bash
## Compare timing of tests files between Haskell, OCaml and Dedukti3
set -euf -o pipefail

timecmd='/usr/bin/time -f %e'

dksrc='DEDUKTI'
mlsrc='OCAML'
hssrc='HASKELL'

files="(cd "${dksrc}" || exit && ls)"

if [[ ! -f "$mlsrc" ]]; then
 svn co 'https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/OCAML'
fi
for lpf in files; do
  root=${lpf%.lp}
  t_lp="$($timecmd lambdapi --verbose 0 "${dksrc}/${lpf}")"
  t_ghcrun="$($timecmd ghcrun "${hssrc}/${root}.hs")"
  t_ocaml="$($timecmd ocaml "${mlsrc}/${root}.ml")"
  # For ghc and ocamlopt, we time compilation and execution
  t_ghc="$($timecmd (cd "${hssrc}" || exit && ghc "${root}.hs" && ./${root}))"
  t_mlopt="$($timecmd (cd "${mlsrc}" || exit && ocamlopt "${root}.ml" && \
          ./a.out))"
  echo -e "${root}: ${t_lp}/${t_ghcrune}/${t_ocaml}/${t_ghc}/${t_mlopt}"
done
