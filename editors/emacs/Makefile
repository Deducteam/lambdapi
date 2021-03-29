VERSION = 1.0

CASK    =
EMACS   = emacs
INSTALL = install

INSTALL_DIR = $(shell opam config var share)/emacs/site-lisp
CURDIR = $(shell pwd)

SRC = $(wildcard *.el)
BUILD_FILES =

# If not using Cask, build only the site file
ifndef CASK
BUILD_FILES += lambdapi-site-file.elc
endif

.PHONY: build
build: $(SRC)
ifdef CASK
	$(CASK) build
else
	$(MAKE) $(BUILD_FILES)
endif

.SUFFIXES = .elc .el
.el.elc:
	$(EMACS) --batch --eval "(add-to-list 'load-path \"$(CURDIR)\")" \
--eval '(byte-compile-file "$<")'

.PHONY: install
install: $(SRC) lambdapi-site-file.elc
	$(INSTALL) -m 644 -t $(INSTALL_DIR) $^
	$(MAKE) clean

.PHONY: dist
dist:
ifdef CASK
	$(CASK) package
endif

.PHONY: test
tests: dist
	./test.sh $(VERSION)

.PHONY: clean
clean:
ifdef CASK
	$(CASK) clean-elc
else
	find . -name '*.elc' -exec rm -f {} \;
endif
