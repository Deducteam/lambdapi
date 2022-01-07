.POSIX:
SRC = $(wildcard *.lp)
OBJ = $(SRC:.lp=.lpo)
.SUFFIXES:

LAMBDAPI = dune exec -- lambdapi

all:
	$(LAMBDAPI) check $(SRC)

install: $(OBJ) lambdapi.pkg
	$(LAMBDAPI) install lambdapi.pkg $(OBJ) $(SRC)

uninstall:
	$(LAMBDAPI) uninstall lambdapi.pkg

clean:
	rm -f $(OBJ)

.SUFFIXES: .lp .lpo

.lp.lpo:
	$(LAMBDAPI) check --gen-obj $<
