# Translating from REC to lambdapi

This directory contains tools to translate files from the
[REC](http://rec.gforge.inria.fr) file format to lp files.  What we do
for the moment is to use the translations from REC to Haskell and then
translate files from haskell to lambdapi.

## Usage

REC files can be retrieved from
<https://scm.gforge.inria.fr/anonscm/svn/rec>.  The haskell files are
in `rec/2019-CONVECS/HASKELL/`.  Then use the awk script,

```bash
./rec_hs_to_lp.awk <INPUT>.hs > <out>.lp
lambdapi out.lp
```

