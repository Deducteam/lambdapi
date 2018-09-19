OCAMLBUILD = ocamlbuild -use-ocamlfind -quiet
CFLAGS     = -cflags -w,A-4-50-9-44-33
DFLAGS     = -docflags -hide-warnings,-charset,utf-8
BINDIR     = $(dir $(shell which ocaml))
VIMDIR     = $(HOME)/.vim
VERSION    = dev

.PHONY: all
all: bin lib

#### Targets #################################################################

.PHONY: help
help:
	@cat MAKEFILE.md

#### Compilation #############################################################

.PHONY: bin
bin: lambdapi.native

lambdapi.native: _build/src/lambdapi.native

_build/src/lambdapi.native: $(wildcard src/*.ml)
	@printf "[OPT] lambdapi.native\n"
	@$(OCAMLBUILD) $(CFLAGS) src/lambdapi.native

.PHONY: lib
lib: _build/src/lambdapi.cma _build/src/lambdapi.cmxa _build/src/lambdapi.cmxs

_build/src/lambdapi.cma: $(wildcard src/*.ml)
	@printf "[BYT] lambdapi.cma\n"
	@$(OCAMLBUILD) $(CFLAGS) src/lambdapi.cma

_build/src/lambdapi.cmxa: $(wildcard src/*.ml)
	@printf "[OPT] lambdapi.cmxa\n"
	@$(OCAMLBUILD) $(CFLAGS) src/lambdapi.cmxa

_build/src/lambdapi.cmxs: $(wildcard src/*.ml)
	@printf "[DYN] lambdapi.cmxs\n"
	@$(OCAMLBUILD) $(CFLAGS) src/lambdapi.cmxs

#### Documentation ###########################################################

.PHONY: doc
doc: lambdapi.docdir/index.html

lambdapi.docdir/index.html: _build/src/lambdapi.docdir/index.html

_build/src/lambdapi.docdir/index.html: $(wildcard src/*.ml)
	@printf "[DOC] lambdapi.docdir/index.html\n"
	@$(OCAMLBUILD) $(DFLAGS) src/lambdapi.docdir/index.html

#### Unit tests ##############################################################

OK_TESTFILES = $(sort $(wildcard tests/OK/*.*))
KO_TESTFILES = $(sort $(wildcard tests/KO/*.*))
TESTFILES    = $(sort $(wildcard examples/*.*))

.PHONY: tests
tests: lambdapi.native
	@printf "## OK tests ##\n"
	@for file in $(OK_TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		&& printf "\033[0;32mOK\033[0m $$file\n" \
	  || { printf "\033[0;31mKO\033[0m $$file\n" \
		&& ./lambdapi.native --verbose 0 $$file ; } ; \
	done
	@printf "## KO tests ##\n"
	@for file in $(KO_TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		&& printf "\033[0;31mOK\033[0m $$file\n" \
		|| printf "\033[0;32mKO\033[0m $$file\n" ; \
	done
	@printf "## Examples ##\n"
	@for file in $(TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
	  && printf "\033[0;32mOK\033[0m $$file\n" \
	  || { printf "\033[0;31mKO\033[0m $$file\n" \
		&& ./lambdapi.native --verbose 0 $$file ; } ; \
	done

.PHONY: real_tests
real_tests: lambdapi.native
	@printf "## OK tests ##\n"
	@for file in $(OK_TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		&& printf "\033[0;32mOK\033[0m $$file\n" \
	  || { printf "\033[0;31mKO\033[0m $$file\n" \
		&& ./lambdapi.native --verbose 0 $$file ; exit 1 ; } ; \
	done
	@printf "## KO tests ##\n"
	@for file in $(KO_TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		&& { printf "\033[0;31mOK\033[0m $$file\n" ; exit 1 ; } \
		|| printf "\033[0;32mKO\033[0m $$file\n" ; \
	done
	@printf "## Examples ##\n"
	@for file in $(TESTFILES) ; do \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
	  && printf "\033[0;32mOK\033[0m $$file\n" \
	  || { printf "\033[0;31mKO\033[0m $$file\n" \
		&& ./lambdapi.native --verbose 0 $$file ; exit 1 ; } ; \
	done

#### Library tests ###########################################################

.PHONY: matita
matita: lambdapi.native
	@printf "## Compiling the Matita's arithmetic library ##\n"
	@cd libraries && ./matita.sh

.PHONY: plein_de_dks
plein_de_dks: lambdapi.native
	@printf "## Compiling “plein de dks” ##\n"
	@cd libraries && ./plein_de_dks.sh

.PHONY: focalide
focalide: lambdapi.native
	@printf "## Compiling focalide library ##\n"
	@cd libraries && ./focalide.sh

.PHONY: holide
holide: lambdapi.native
	@printf "## Compiling holide library ##\n"
	@cd libraries && ./holide.sh

.PHONY: verine
verine: lambdapi.native
	@printf "## Compiling verine library ##\n"
	@cd libraries && ./verine.sh

.PHONY: iprover
iprover: lambdapi.native
	@printf "## Compiling iProverModulo library ##\n"
	@cd libraries && ./iprover.sh

.PHONY: dklib
dklib: lambdapi.native
	@printf "## Compiling the dklib library ##\n"
	@cd libraries && ./dklib.sh

.PHONY: zenon_modulo
zenon_modulo: lambdapi.native
	@printf "## Compiling the zenon library ##\n"
	@cd libraries && ./zenon_modulo.sh

#### Cleaning targets ########################################################

.PHONY: clean
clean:
	@$(OCAMLBUILD) -clean

.PHONY: distclean
distclean: clean
	@cd libraries && ./matita.sh clean
	@cd libraries && ./plein_de_dks.sh clean
	@cd libraries && ./focalide.sh clean
	@cd libraries && ./holide.sh clean
	@cd libraries && ./verine.sh clean
	@cd libraries && ./iprover.sh clean
	@cd libraries && ./dklib.sh clean
	@cd libraries && ./zenon_modulo.sh clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.dko" -exec rm {} \;
	@rm -f META

.PHONY: fullclean
fullclean: distclean
	@cd libraries && ./matita.sh fullclean
	@cd libraries && ./plein_de_dks.sh fullclean
	@cd libraries && ./focalide.sh fullclean
	@cd libraries && ./holide.sh fullclean
	@cd libraries && ./verine.sh fullclean
	@cd libraries && ./iprover.sh fullclean
	@cd libraries && ./dklib.sh fullclean
	@cd libraries && ./zenon_modulo.sh fullclean

#### Installation targets ####################################################

# META generation.
META: GNUmakefile
	@printf "[GEN] $@ (version $(VERSION))\n"
	@printf "name            = \"lambdapi\"\n"                              > $@
	@printf "version         = \"$(VERSION)\"\n"                           >> $@
	@printf "requires        = \"unix,earley,earley.str,bindlib,timed\"\n" >> $@
	@printf "description     = \"The Lambdapi prover as a library\"\n"     >> $@
	@printf "archive(byte)   = \"lambdapi.cma\"\n"                         >> $@
	@printf "plugin(byte)    = \"lambdapi.cma\"\n"                         >> $@
	@printf "archive(native) = \"lambdapi.cmxa\"\n"                        >> $@
	@printf "plugin(native)  = \"lambdapi.cmxs\"\n"                        >> $@

# Uninstalling everything.
.PHONY: uninstall
uninstall:
	@ocamlfind remove lambdapi
	@rm -f $(BINDIR)/lambdapi

# Install the main program.
.PHONY: install
install: lambdapi.native META uninstall lib
	@ocamlfind install lambdapi META  _build/src/lambdapi.cmxa \
		_build/src/lambdapi.a _build/src/lambdapi.cma _build/src/lambdapi.cmxs \
		$(wildcard _build/src/*.cmi) $(wildcard _build/src/*.cmx) \
		$(wildcard _build/src/*.o) $(wildcard _build/src/*.ml)
	@install -m 755 $< $(BINDIR)/lambdapi

# Install for the vim mode (in the user's directory).
.PHONY: install_vim
install_vim: $(wildcard editors/vim/*/*.vim)
ifeq ($(wildcard $(VIMDIR)/.),)
	@printf "\e[36mWill not install vim mode.\e[39m\n"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/dedukti.vim    $(VIMDIR)/syntax
	install -m 644 editors/vim/syntax/lambdapi.vim   $(VIMDIR)/syntax
	install -m 644 editors/vim/ftdetect/dedukti.vim  $(VIMDIR)/ftdetect
	install -m 644 editors/vim/ftdetect/lambdapi.vim $(VIMDIR)/ftdetect
	@printf "\e[36mVim mode installed.\e[39m\n"
endif
