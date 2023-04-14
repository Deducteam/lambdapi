SRC := $(wildcard *.dk)

default: $(SRC:%.dk=%.v)

LAMBDAPI = lambdapi export -o stt_coq --encoding ../encoding.lp --erasing ../erasing.lp --renaming ../renaming.lp --requiring coq.v --no-implicits

%.v: %.dk
	$(LAMBDAPI) $< > $@

.PHONY: dko
dko: $(SRC:%.dk=%.dko)

hol.dko: hol.dk
	dk check -e $@

%.dko: %.dk hol.dko
	dk check $*.dk
