SRC := $(wildcard *.v)

default: $(SRC:%.v=%.vo)

hol.vo: hol.v
	coqc $<

%.vo: %.v hol.vo
	coqc $*.v

clean:
	rm -f *.vo
