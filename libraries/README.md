How to translate the Holide library to Coq?
-------------------------------------------

From the root of the project do:
```
make holide
cd libraries/holide
../patch-holide-dkfiles.sh
# dk check -e STTfa.dk
# dk check -e hol.dk
# dk check *.dk
../dk2coq.sh *.dk
cp -f ../Coq.v STTfa.v
../check-holide-vfiles.sh
```
