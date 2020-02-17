#!/usr/bin/python3

import sys
import os
import subprocess
import timeit

srcdk = "DEDUKTI"
srchs = "HASKELL"
srcml = "OCAML"
svnrep = "https://scm.gforge.inria.fr/anonscm/svn/rec/2019-CONVECS/"

null = open(os.devnull, "w")
timeout = 60 * 30  # In seconds

def interpret(exe, f):
    tim = timeit.Timer(stmt=lambda:subprocess.check_call([exe, f],
        stdout=null, stderr=null, timeout=timeout))
    try:
        return tim.timeit(number=1)
    except subprocess.CalledProcessError:
        return "N/A"
    except subprocess.TimeoutExpired:
        return "TO"


def ocamlopt(f):
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


def ghc(root):
    exe = os.path.join(srchs, root)
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
    if not os.path.exists(srchs):
        subprocess.call(["svn", "co", svnrep + srchs])
    if not os.path.exists(srcdk):
        produce_dk()
    if not os.path.exists(srcml):
        subprocess.call(["svn", "co", svnrep + srcml])


"""Translate haskell files to dedukti with awk script"""
def produce_dk():
    os.mkdir(srcdk, mode=0o755)
    for f in os.listdir(srchs):
        # Skip conditional rewriting
        if not subprocess.call(["grep", "==\|=/=", f]):
            root = os.path.splitext(os.path.basename(f))
            out = os.path.join(srcdk, dk + ".lp")
            with open(out, "w") as o:
                subprocess.check_call(["./rec_hs_to_lp.awk", f], stdout=o)

def main():
    check_paths()
    root = lambda x: os.path.splitext(os.path.basename(x))[0]
    files = [root(f) for f in os.listdir(srcdk)]
    frecs = [{"lp": os.path.join(srcdk, r + ".lp"),
              "hs": os.path.join(srchs, r + ".hs"),
              "ml": os.path.join(srcml, r + ".ml"),
              "root": r} for r in files]
    print("\\begin{tabular}{l r r r r r}\n"
          "\toprule\n"
          "& Dedukti & \\texttt{runghc} & \\texttt{ocaml} & "
          "\\texttt{ghc} & \\texttt{ocamlopt}\\\\\n"
          "\\midrule\n")
    for fs in frecs:
        tlp = interpret("lambdapi", fs["lp"])
        trunghc = interpret("runghc", fs["hs"])
        tocaml = interpret("ocaml", fs["ml"])
        tghc = ghc(fs["root"])
        tmlopt = ocamlopt(fs["ml"])
        print("{} & {} & {} & {} & {} & {}\\\\".format(
            fs["root"], tlp, trunghc, tocaml,
            tghc, tmlopt))
    print("\\bottomrule\n"
          "\\end{tabular}\n")

if __name__ == "__main__":
    main()
