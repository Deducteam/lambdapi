MAKEFLAGS += -r -k -j$(shell nproc)

LPO_MK := lpo.mk

EXCLUDE := _opam
EXCEPT := $(EXCLUDE:%=! -path './%/*')

LP := $(shell find . $(EXCEPT) -name '*.lp' -print)
DK := $(shell find . $(EXCEPT) -name '*.dk' -print)
LPO := $(LP:%.lp=%.lpo) $(DK:%.dk=%.lpo)

.PHONY: default
default: $(LPO)

LP_OPTIONS = -c -v 0

%.lpo: %.lp
	@echo lambdapi check $< ...
	@lambdapi check $(LP_OPTIONS) $<

%.lpo: %.dk
	@echo lambdapi check $< ...
	@lambdapi check $(LP_OPTIONS) $<

include $(LPO_MK)

$(LPO_MK): lambdapi.pkg $(LP)
	@echo create/update $@ ...
	@lambdapi depend > $@

.PHONY: clean
clean:
	-find . $(EXCEPT) -name '*.lpo' -delete
	-rm $(LPO_MK)

.PHONY: install
install: lambdapi.pkg $(LP) $(LPO)
	@echo lambdapi install ...
	@lambdapi install

.PHONY: uninstall
uninstall: lambdapi.pkg
	@echo lambdapi uninstall ...
	@lambdapi uninstall
