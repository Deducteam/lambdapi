PKG := TFF U Zenon

.PHONY: default
default:
	for p in $(PKG); do $(MAKE) -C $$p; done

%:
	for p in $(PKG); do $(MAKE) -C $$p $*; done
