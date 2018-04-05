OCAMLBUILD = ocamlbuild -use-ocamlfind -quiet
BINDIR     = $(dir $(shell which ocaml))
VIMDIR     = $(HOME)/.vim

#### Compilation #############################################################

.PHONY: all
all: lambdapi.native

lambdapi.native: _build/src/lambdapi.native

_build/src/lambdapi.native: $(wildcard src/*.ml)
	$(OCAMLBUILD) src/lambdapi.native

#### Unit tests ##############################################################

OK_TESTFILES = $(wildcard tests/OK/*.dk)
KO_TESTFILES = $(wildcard tests/KO/*.dk)
TESTFILES    = $(wildcard examples/*.dk)

.PHONY: tests
tests: lambdapi.native
	@echo "## OK tests ##"
	@rm -f $(OK_TESTFILES:.dk=.dko)
	@for file in $(OK_TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;32mOK\033[0m $$file"   \
	    || echo -e "\033[0;31mKO\033[0m $$file" ; \
	done
	@echo "## KO tests ##"
	@rm -f $(KO_TESTFILES:.dk=.dko)
	@for file in $(KO_TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;31mOK\033[0m $$file"   \
			|| echo -e "\033[0;32mKO\033[0m $$file" ; \
	done
	@echo "## Examples ##"
	@rm -f $(TESTFILES:.dk=.dko)
	@for file in $(TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;32mOK\033[0m $$file"   \
	    || echo -e "\033[0;31mKO\033[0m $$file" ; \
	done

#### Library tests ###########################################################

.PHONY: matita
matita: lambdapi.native
	@echo "## Compiling the Matita's arithmetic library ##"
	@cd libraries && ./matita.sh

.PHONY: plein_de_dks
plein_de_dks: lambdapi.native
	@echo "## Compiling “plein de dks” ##"
	@cd libraries && ./plein_de_dks.sh

.PHONY: focalide
focalide: lambdapi.native
	@echo "## Compiling focalide library ##"
	@cd libraries && ./focalide.sh

.PHONY: holide
holide: lambdapi.native
	@echo "## Compiling holide library ##"
	@cd libraries && ./holide.sh

.PHONY: verine
verine: lambdapi.native
	@echo "## Compiling verine library ##"
	@cd libraries && ./verine.sh

.PHONY: iprover
iprover: lambdapi.native
	@echo "## Compiling iProverModulo library ##"
	@cd libraries && ./iprover.sh

.PHONY: dklib
dklib: lambdapi.native
	@echo "## Compiling the dklib library ##"
	@cd libraries && ./dklib.sh

.PHONY: zenon
zenon: lambdapi.native
	@echo "## Compiling the zenon library ##"
	@cd libraries/zenon && ./zenon.sh

#### Cleaning targets ########################################################

.PHONY: clean
clean:
	@ocamlbuild -clean

.PHONY: distclean
distclean: clean
	@cd libraries && ./plein_de_dks.sh clean
	@cd libraries && ./focalide.sh clean
	@cd libraries && ./holide.sh clean
	@cd libraries && ./iprover.sh clean
	@cd libraries && ./verine.sh clean
	@cd libraries && ./dklib.sh clean
	@cd libraries/zenon && ./zenon.sh clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.dko" -exec rm {} \;

.PHONY: fullclean
fullclean: distclean
	@cd libraries && ./plein_de_dks.sh fullclean
	@cd libraries && ./matita.sh fullclean
	@cd libraries && ./focalide.sh fullclean
	@cd libraries && ./holide.sh fullclean
	@cd libraries && ./iprover.sh fullclean
	@cd libraries && ./verine.sh fullclean
	@cd libraries && ./dklib.sh fullclean
	@cd libraries/zenon && ./zenon.sh fullclean

#### Installation targets ####################################################

# Install the main program.
.PHONY: install
install: lambdapi.native
	install -m 755 $^ $(BINDIR)

# Install for the vim mode (in the user's directory).
.PHONY: install_vim
install_vim: editors/vim/ftdetect/dedukti.vim editors/vim/syntax/dedukti.vim
ifeq ($(wildcard $(VIMDIR)/.),)
	@echo -e "\e[36mWill not install vim mode.\e[39m"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/dedukti.vim $(VIMDIR)/syntax
	install -m 644 editors/vim/ftdetect/dedukti.vim $(VIMDIR)/ftdetect
	@echo -e "\e[36mVim mode installed.\e[39m"
endif
