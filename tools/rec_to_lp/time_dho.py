#!/usr/bin/python

import sys
import os
import subprocess
import timeit

srcdk="DEDUKTI"
srchs="HASKELL"
srcml="OCAML"
svnrep="https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/"


def interpret(exe, f):
    args = [exe, f]
    return subprocess.check_call([exe, f])

def main():
    root = lambda x: os.path.splitext(os.path.basename(x))[0]
    files = [root(f) for f in os.listdir(srcdk)]
    if not os.path.exists(srcml):
        subprocess.call(["svn", "co", svnrep + srcml])
    frecs = [{"lp": os.path.join(srcdk, r + ".lp"),
              "hs": os.path.join(srchs, r + ".hs"),
              "ml": os.path.join(srcml, r + ".ml"),
              "root": r} for r in files]
    for fs in frecs:
        tlp = timeit.timeit(interpret("lambdapi", fs["lp"]))
        trunghc = timeit.timeit(interpret("runghc", fs["hs"]))
        tocaml = timeit.timeit(interpret("ocaml", fs["ml"]))
        print("{}: {}/{}/{}".format(fs["root"], fs["lp"], fs["hs"], fs["ml"]))
