#!/usr/bin/python3

import sys
import os
import subprocess
import timeit
from glob import glob

srcdk = "DEDUKTI"
src = { "hs": "HASKELL",
        "ml": "OCAML",
        "co": "CAFEOBJ-B",
        "ma": "MAUDE" }
"""Mapping from system code to folder name containing rec tests."""
svnrep = "https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/"

null = open(os.devnull, "w")
timeout = 60 * 30  # 30 min (unit is seconds)

def interpret(exe, f: str) -> str:
    print("{}".format(exe + [f]), end='\r')
    tim = timeit.Timer(stmt=lambda:subprocess.check_call(exe + [f],
        stdout=null, stderr=null, timeout=timeout))
    try:
        return tim.timeit(number=1)
    except subprocess.CalledProcessError:
        return "N/A"
    except subprocess.TimeoutExpired:
        return "T/O"


def ocamlopt(f: str) -> str:
    def cnr():
        print("\r{}".format(["ocamlopt", f]), end='\r')
        subprocess.check_call(["ocamlopt", f], stdout=null, stderr=null,
                timeout=timeout)
        print("\r{}".format(["./a.out"]))
        subprocess.check_call(["./a.out"], stdout=null, stderr=null,
                              timeout=timeout)
    tim = timeit.Timer(stmt=cnr)
    try:
        return tim.timeit(number=1)
    except subprocess.CalledProcessError:
        return "N/A"
    except subprocess.TimeoutExpired:
        return "T/O"


def ghc(root: str) -> str:
    exe = os.path.join(src["hs"], root)
    fil = exe + ".hs"
    def cnr():
        print("\r{}".format(["ghc", fil]), end='\r')
        subprocess.check_call(["ghc", fil], stdout=null, timeout=timeout)
        print("\r{}".format([exe]), end='\r')
        subprocess.check_call([exe], stdout=null, timeout=timeout)
    tim = timeit.Timer(stmt=cnr)
    try:
        return tim.timeit(number=1)
    except subprocess.CalledProcessError:
        return "N/A"
    except subprocess.TimeoutExpired:
        return "T/O"


"""Check that sources are present and download them if necessary"""
def check_paths():
    for rep in src.values():
        subprocess.call(["svn", "co", "-q", svnrep + rep])
    if not os.path.exists(srcdk):
        produce_dk()


"""Returns the filename without extension, without path."""
def pure_name(fname):
    return os.path.splitext(os.path.basename(fname))[0]


"""Translate haskell files to dedukti with awk script"""
def produce_dk():
    os.mkdir(srcdk, mode=0o755)
    for f in glob("{}/*.hs".format(src["hs"])):
        # Skip conditional rewriting
        if subprocess.call(["grep", '==\|=/=', "-q", f]):
            out = os.path.join(srcdk, pure_name(f) + ".lp")
            with open(out, "w") as o:
                subprocess.check_call(["./rec_hs_to_lp.awk", f],
                                      stdout=o)
    with open(os.path.join(srcdk, "lamdapi.pkg"), "w") as lpkg:
        lpkg.writelines(["package_name = rec", "root_path = rec"])

def main():
    check_paths()
    files = [pure_name(f) for f in os.listdir(srcdk)]
    frecs = [{"lp": os.path.join(srcdk, r + ".lp"),
              "hs": os.path.join(src["hs"], r + ".hs"),
              "ml": os.path.join(src["ml"], r + ".ml"),
              "co": os.path.join(src["co"], r + ".mod"),
              "ma": os.path.join(src["ma"], r + ".maude"),
              "root": r} for r in files]
    with open("rectime.csv", "w") as out:
        out.write(",".join(["Dedukti", "CajeOBJ", "Maude",
                            "runghc", "ocaml", "ghc", "ocamlopt"]))
        out.write("\n")
    for fs in frecs:
        timings = [
            interpret(["lambdapi", "check"], fs["lp"]),
            interpret(["cafeobj", "-batch"], fs["co"]),
            interpret(["maude", "-batch"], fs["ma"]),
            interpret(["runghc"], fs["hs"]),
            interpret(["ocaml"], fs["ml"]),
            ghc(fs["root"]),
            ocamlopt(fs["ml"])
        ]
    with open("rectime.csv", "a") as out:
            out.write(",".join(timings))
            out.write("\n")

if __name__ == "__main__":
    main()
