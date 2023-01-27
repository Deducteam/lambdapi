#!/bin/sh
set -e
set -x

export PATH=$PWD/_build/install/default/bin:$PATH
cd out
lambdapi check --lib-root . -c coq/cupicef.lp
lambdapi check --lib-root . -c Coq__Init__Logic.lp
lambdapi check --lib-root . -c Coq__Init__Datatypes.dk