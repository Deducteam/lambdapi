.POSIX:
SRC = $(wildcard *.lp)
OBJ = $(SRC:.lp=.lpo)
.SUFFIXES:

all: $(OBJ)

install: $(OBJ) lambdapi.pkg
	lambdapi install lambdapi.pkg $(OBJ) $(SRC)

uninstall:
	lambdapi uninstall lambdapi.pkg

clean:
	rm -f $(OBJ)

.SUFFIXES: .lp .lpo

.lp.lpo:
	lambdapi check --gen-obj $<
