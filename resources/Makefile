MAKEFLAGS += -r -k -j$(shell nproc)

LPO_MK := lpo.mk

EXCLUDE := _opam
EXCEPT := $(EXCLUDE:%=! -path './%/*')

LP := $(shell find . -name '*.lp' $(EXCEPT) -print)
LPO := $(LP:%=%o)

.PHONY: default
default: $(LPO)

LP_OPTIONS = -c -v 0

%.lpo: %.lp
	@echo lambdapi check $< ...
	@lambdapi check $(LP_OPTIONS) $<

include $(LPO_MK)

$(LPO_MK): $(LP)
	@echo create/update $@ ...
	@lambdapi depend > $@

.PHONY: clean
clean:
	-find . -name '*.lpo' $(EXCEPT) -delete
	-rm $(LPO_MK)

.PHONY: install
install: lambdapi.pkg $(LP) $(LPO)
	@echo lambdapi install ...
	@lambdapi install

.PHONY: uninstall
uninstall: lambdapi.pkg
	@echo lambdapi uninstall ...
	@lambdapi uninstall $+
