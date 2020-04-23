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
    tim = timeit.Timer(stmt=lambda:subprocess.check_call(exe + [f],
        stdout=null, stderr=null, timeout=timeout))
    try:
        return tim.timeit(number=1)
    except subprocess.CalledProcessError:
        return "N/A"
    except subprocess.TimeoutExpired:
        return "TO"


def ocamlopt(f: str) -> str:
    def cnr():
        subprocess.check_call(["ocamlopt", f], stdout=null, stderr=null,
                timeout=timeout)
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
        subprocess.check_call(["ghc", fil], stdout=null, timeout=timeout)
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
    print("\\begin{tabular}{l r r r r r}\n"
          "\toprule\n"
          "& Dedukti & \\texttt{cafeobj} & \\texttt{maude} & "
          "\\texttt{runghc} & \\texttt{ocaml} & "
          "\\texttt{ghc} & \\texttt{ocamlopt}\\\\\n"
          "\\midrule\n")
    for fs in frecs:
        tlp = interpret(["lambdapi", "check"], fs["lp"])
        tcafeobj = interpret(["cafeobj"], fs["co"])
        tmaude = interpret(["maude"], fs["ma"])
        trunghc = interpret(["runghc"], fs["hs"])
        tocaml = interpret(["ocaml"], fs["ml"])
        tghc = ghc(fs["root"])
        tmlopt = ocamlopt(fs["ml"])
        print("{} & {} & {} & {} & {} & {} & {} & {}\\\\".format(
            fs["root"], tlp, tcafeobj, tmaude, trunghc, tocaml,
            tghc, tmlopt))
    print("\\bottomrule\n"
          "\\end{tabular}\n")

if __name__ == "__main__":
    main()
