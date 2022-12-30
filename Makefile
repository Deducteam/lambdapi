VIMDIR = $(HOME)/.vim
EMACS  = $(shell which emacs)

LIB_ROOT := $(shell\
  if test -n "$(LAMBDAPI_LIB_ROOT)";\
  then echo $(LAMBDAPI_LIB_ROOT);\
  else\
    if test -n "$(OPAM_SWITCH_PREFIX)";\
    then echo $(OPAM_SWITCH_PREFIX);\
    else echo /usr/local;\
    fi;\
  fi)/lib/lambdapi/lib_root

#### Compilation (binary, library and documentation) #########################

.PHONY: all
all: bin

.PHONY: bin
bin:
	@dune build --only-packages lambdapi @install

.PHONY: odoc
odoc:
	@dune build --only-packages lambdapi @doc

.PHONY: doc
doc: bnf
	$(MAKE) -C doc html

.PHONY: bnf
bnf:
	$(MAKE) -C doc -f Makefile.bnf

#### Unit tests and sanity check #############################################

.PHONY: tests
tests: bin
	mkdir -p $(LIB_ROOT)
	@dune runtest
	@dune exec --only-packages lambdapi -- tests/runtests.sh
	@dune exec --only-packages lambdapi -- tests/dtrees.sh
	@dune exec --only-packages lambdapi -- tests/export_dk.sh
	@dune exec --only-packages lambdapi -- tests/export_lp.sh

.PHONY: tests_alt_ergo
tests_alt_ergo: bin
	@dune exec --only-packages lambdapi -- lambdapi check tests/OK/why3*.lp

.PHONY: sanity_check
sanity_check: misc/sanity_check.sh
	@./$<

#### Library tests ###########################################################

.PHONY: matita
matita: bin
	@printf "## Compiling the Matita's arithmetic library ##\n"
	@cd libraries && dune exec -- ./matita.sh

.PHONY: focalide
focalide: bin
	@printf "## Compiling focalide library ##\n"
	@cd libraries && dune exec -- ./focalide.sh

.PHONY: holide
holide: bin
	@printf "## Compiling holide library ##\n"
	@cd libraries && dune exec -- ./holide.sh

.PHONY: verine
verine: bin
	@printf "## Compiling verine library ##\n"
	@cd libraries && dune exec -- ./verine.sh

.PHONY: iprover
iprover: bin
	@printf "## Compiling iProverModulo library ##\n"
	@cd libraries && dune exec -- ./iprover.sh

.PHONY: dklib
dklib: bin
	@printf "## Compiling the dklib library ##\n"
	@cd libraries && dune exec -- ./dklib.sh

.PHONY: zenon_modulo
zenon_modulo: bin
	@printf "## Compiling the zenon library ##\n"
	@cd libraries && dune exec -- ./zenon_modulo.sh

#### Cleaning targets ########################################################

.PHONY: lpoclean
lpoclean:
	@find . -type f -name "*.lpo" -exec rm {} \;

.PHONY: clean
clean: lpoclean
	@dune clean
	@$(MAKE) -C editors/emacs clean
	@$(MAKE) -C editors/vscode clean
	@$(MAKE) -C Logic clean

.PHONY: distclean
distclean: clean
	@cd libraries && ./matita.sh clean
	@cd libraries && ./focalide.sh clean
	@cd libraries && ./holide.sh clean
	@cd libraries && ./verine.sh clean
	@cd libraries && ./iprover.sh clean
	@cd libraries && ./dklib.sh clean
	@cd libraries && ./zenon_modulo.sh clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.gv" -exec rm {} \;

.PHONY: fullclean
fullclean: distclean
	@cd libraries && ./matita.sh fullclean
	@cd libraries && ./focalide.sh fullclean
	@cd libraries && ./holide.sh fullclean
	@cd libraries && ./verine.sh fullclean
	@cd libraries && ./iprover.sh fullclean
	@cd libraries && ./dklib.sh fullclean
	@cd libraries && ./zenon_modulo.sh fullclean

#### Installation and release targets ########################################

.PHONY: install
install: bin
	@dune install lambdapi
	@mkdir -p $(LIB_ROOT)
	@echo default lib root: $(LIB_ROOT)

.PHONY: uninstall
uninstall:
	@dune uninstall lambdapi

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

.PHONY: install_emacs
install_emacs:
ifeq ($(EMACS),)
	@printf "\e[36mNo 'emacs' binary available in path and EMACS variable \
is not set, \nEmacs mode won't be installed.\e[39m\n"
else
	@dune build --only-packages lambdapi-mode @install
	@dune install lambdapi-mode
	@printf "\e[36mEmacs mode installed.\e[39m\n"
endif
