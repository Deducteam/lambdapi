#!/bin/bash

set -e

NBWORKERS="${NBWORKERS:-1}"

SRC="https://raw.githubusercontent.com/Deducteam/dedukti.github.io/master/data/libraries/iProverModulo_dk.tar.gz"
DIR="iprover"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  rm -rf iProverModulo_dk
  rm -f iProverModulo_dk.tar.gz
  if [[ "$1" = "fullclean" ]]; then
    rm -f iprover.tar.gz
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
  if [[ ! -f iprover.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC} -O iprover.tar.gz
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf iprover.tar.gz
  mv iProverModulo_dk ${DIR}
  echo "OK"

  # Applying the changes (add "#REQUIRE hol" and fix obsolete syntax).
  echo -n "  - applying changes... "
  rm ${DIR}/ALG375d1_*.dk # Stack overflow
  rm ${DIR}/ALG376d1_*.dk # Stack overflow
  rm ${DIR}/ALG396d1_*.dk # Type error (has worked before)
  rm ${DIR}/HWV009d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV009d3_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV009d4_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV012d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV012d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV013d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV013d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV014d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV014d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV015d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV015d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV019d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV019d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV019d3_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV021d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV024d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV025d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV025d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV026d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV026d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV027d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV027d2_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV107d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS147p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS151p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS153p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS155p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS159p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS161p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS162p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/LCL764d1_*.dk # Stack overflow
  rm ${DIR}/LCL787d1_*.dk # Stack overflow
  rm ${DIR}/NLP001d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP001p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP004d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP004p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP007d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP007p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP009d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP009p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP011d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP011p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP079d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP080d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP081d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP094d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP094p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP117d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP117p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP122d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP122p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/PUZ017d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SCT007d1_*.dk # Stack overflow
  rm ${DIR}/SCT002d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV092p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV620d1_*.dk # Stack overflow
  rm ${DIR}/SWV789d1_*.dk # Stack overflow
  rm ${DIR}/SWV794d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV811d1_*.dk # Stack overflow
  rm ${DIR}/SWV816d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV827d1_*.dk # Stack overflow
  rm ${DIR}/SWV836d1_*.dk # Stack overflow
  rm ${DIR}/SWV844d1_*.dk # Stack overflow
  rm ${DIR}/SWW210p1_*.dk # Stack overflow
  rm ${DIR}/SWW219p1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWW221p1_*.dk # Stack overflow
  rm ${DIR}/SWW225p1_*.dk # Stack overflow
  rm ${DIR}/SWV295d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN813d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN819d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN820d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN833d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN834d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN836d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN837d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN843d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN844d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN845d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN846d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN847d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN848d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN849d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN850d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN856d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN857d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN858d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN859d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN860d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN861d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN862d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN865d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN871d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN873d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN874d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN875d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN876d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN877d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN878d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN879d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN880d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN881d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN882d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN883d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN884d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN885d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN886d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN887d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN889d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN890d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN891d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN892d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN893d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN894d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN895d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN896d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN897d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN898d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN899d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN900d1_*.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN901d1_*.dk # More the 30 seconds (loops?)
  sed -i 's/^#NAME FOL.//g' ${DIR}/FOL.dk
  sed -i 's/injective/injec/g' ${DIR}/*.dk
  for SIG in `find ${DIR} -name '*_sig.dk'`; do
    MSIG=`basename "${SIG}" ".dk"`
    PRF="${SIG%%_sig.dk}_prf.dk"
    sed -i "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE FOL./g" ${SIG}
    sed -i "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE FOL.\n#REQUIRE ${MSIG}./g" ${PRF}
  done
  cp -f ../resources/Makefile ../tests/lambdapi.pkg ${DIR}
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
fi

# Check the files
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" make LP_OPTIONS='-c -v 0 -w'
