#!/bin/bash

NBWORKERS="${NBWORKERS:-1}"

SRC="https://deducteam.github.io/data/libraries/iProverModulo_dk.tar.gz"
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
  sed -i "s/^#NAME FOL.//g" "${DIR}/FOL.dk"
  for SIG in `find ${DIR} -type f -name "*_sig.dk"`; do
    MSIG=`basename "${SIG}" ".dk"`
    PRF="${SIG%%_sig.dk}_prf.dk"
    sed -i "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE FOL./g" ${SIG}
    sed -i "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE FOL.\n#REQUIRE ${MSIG}./g" ${PRF}
  done
  echo "OK"

  # Blacklist.
  rm ${DIR}/ALG375d1_prf.dk # Stack overflow
  rm ${DIR}/ALG376d1_prf.dk # Stack overflow
  rm ${DIR}/ALG396d1_prf.dk # Type error (has worked before)
  rm ${DIR}/HWV009d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV009d3_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV009d4_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV012d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV012d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV013d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV013d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV014d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV014d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV015d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV015d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV019d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV019d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV019d3_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV021d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV021d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV024d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV025d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV025d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV025d3_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV026d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV026d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV026d3_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV027d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV027d2_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/HWV107d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS147p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS151p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS153p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS155p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS159p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS161p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/KRS162p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/LCL764d1_prf.dk # Stack overflow
  rm ${DIR}/LCL787d1_prf.dk # Stack overflow
  rm ${DIR}/NLP001d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP001p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP004d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP004p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP007d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP007p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP009d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP009p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP011d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP011p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP079d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP080d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP081d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP094d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP094p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP117d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP117p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP122d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/NLP122p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/PUZ017d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SCT007d1_prf.dk # Stack overflow
  rm ${DIR}/SWV092p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV611d1_prf.dk # Stack overflow
  rm ${DIR}/SWV620d1_prf.dk # Stack overflow
  rm ${DIR}/SWV789d1_prf.dk # Stack overflow
  rm ${DIR}/SWV794d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV811d1_prf.dk # Stack overflow
  rm ${DIR}/SWV816d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWV826d1_prf.dk # Stack overflow
  rm ${DIR}/SWV827d1_prf.dk # Stack overflow
  rm ${DIR}/SWV836d1_prf.dk # Stack overflow
  rm ${DIR}/SWV844d1_prf.dk # Stack overflow
  rm ${DIR}/SWW210p1_prf.dk # Stack overflow
  rm ${DIR}/SWW219p1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SWW221p1_prf.dk # Stack overflow
  rm ${DIR}/SWW225p1_prf.dk # Stack overflow
  rm ${DIR}/SYN813d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN819d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN820d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN833d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN834d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN836d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN837d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN843d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN844d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN845d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN846d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN847d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN848d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN849d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN850d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN856d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN857d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN858d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN859d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN860d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN861d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN862d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN865d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN866d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN869d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN871d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN873d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN874d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN875d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN876d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN877d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN878d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN879d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN880d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN881d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN882d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN883d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN884d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN885d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN886d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN887d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN889d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN890d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN891d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN892d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN893d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN894d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN895d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN896d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN897d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN898d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN899d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN900d1_prf.dk # More the 30 seconds (loops?)
  rm ${DIR}/SYN901d1_prf.dk # More the 30 seconds (loops?)

  # Cleaning up.
  echo -n "  - cleaning up...      "
  rm ${DIR}/Makefile
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
else
  # Cleaning up build directory
  rm -f ${DIR}/*.lpo
  rm -f ${DIR}/error.log
fi

# Check the files
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" \
  lambdapi check --lib-root . --no-warnings *_prf.dk
