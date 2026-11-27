How to translate the Holide Dedukti library to Rocq?
-------------------------------------------

Extracting and patching the Holide library:
```
make holide
cd libraries/holide
../patch-filenames.sh
cp . ../holide-bak
```

Checking the Holide dk files (optional):
```
make -j 7 -f ../coq2dk dko
```

To translate Holide dk files to Rocq, we need to patch those dk files a little bit. See the sources of the following scripts for details.

Convert the Holide dk files to raw Rocq files, and check them:
```
../dk2rawcoq.sh
```

Convert the Holide dk files to Rocq files using the fact that the Holide dk files use an encoding of simple type theory, and check them:
```
../dk2sttcoq.sh
```
