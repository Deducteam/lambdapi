#!/bin/bash

LAMBDAPI="../../lambdapi.native"
SRC="https://git.lsv.fr/genestier/PleinDeDk/repository/master/archive.tar.gz"
DIR="plein_de_dks"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  rm -rf PleinDeDk-*
  if [[ "$1" = "fullclean" ]]; then
    rm -f ${DIR}.tar.gz
  fi
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
  echo "Invalid argument, usage: $0 [clean | fullclean]"
  exit -1
fi

# Prepare the library if necessary.
if [[ ! -d ${DIR} ]]; then
  # The directory is not ready, so we need to work.
  echo "Preparing the library:"

  # Download the library if necessary.
  if [[ ! -f ${DIR}.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC} -O ${DIR}.tar.gz
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf ${DIR}.tar.gz
  mv PleinDeDk-* ${DIR}
  echo "OK"

  # Cleaning up.
  echo -n "  - cleaning up...      "
  rm ${DIR}/.gitignore ${DIR}/removeConneries.py ${DIR}/removeTypeCtx.py
  rm -r ${DIR}/CoqModels ${DIR}/Paradoxes ${DIR}/Sudoku
  rm -r ${DIR}/TermChecker ${DIR}/Theories
  mv ${DIR}/Miscellaneous/*.dk ${DIR}
  rm -r ${DIR}/Miscellaneous
  # Black list (to fix)
  rm ${DIR}/andPoly.dk
  rm ${DIR}/associativity.dk
  rm ${DIR}/badlyTypedLhs.dk
  rm ${DIR}/cic.dk
  rm ${DIR}/bugRaphael.dk
  rm ${DIR}/examplesBJO.dk
  rm ${DIR}/explFrc.dk
  rm ${DIR}/fixpoint.dk
  rm ${DIR}/identiteListe_pbArite.dk
  rm ${DIR}/intBinaire.dk
  rm ${DIR}/McCarthy.dk
  rm ${DIR}/miller.dk
  rm ${DIR}/monad.dk
  rm ${DIR}/nat_prop.dk
  rm ${DIR}/numberBases.dk
  rm ${DIR}/pureLambdaCalculus.dk
  rm ${DIR}/simplyTypedLambdaCalculus.dk
  rm ${DIR}/syracuse.dk
  rm ${DIR}/tuto.dk
  rm ${DIR}/vectDependant_InjectivityIsCrucial.dk
  rm ${DIR}/wahlstedt.dk
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
fi

# Checking function.
function check_plein_de_dks() {
  for FILE in `ls *.dk`; do
    ${LAMBDAPI} ${FILE}
  done
}

# Export stuff for the checking function.
export readonly LAMBDAPI=${LAMBDAPI}
export -f check_plein_de_dks

# Run the actual checks.
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" bash -c "check_plein_de_dks"
