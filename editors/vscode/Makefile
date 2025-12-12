default: compile

compile: node_modules
	npm run compile

node_modules:
	npm install

clean:
	rm -rf node_modules out

VSCE = $(shell which vsce)
JQ = $(shell which jq)
ifneq ($(VSCE),)
ifneq ($(JQ),)
VERSION = $(shell cat package.json | jq '.version')
endif

.PHONY: install_local
install_local: compile
ifeq ($(VERSION),)
	@echo 'jq not found. Please install with sudo apt install jq or export version before calling install_local (PLEASE use same as in package.json): VERSION=X.Y.Z make install_local'
else
	vsce package
	code --install-extension lambdapi-$(VERSION).vsix
endif

else
install_local:
	@echo 'vsce not found. Please install with npm install -g @vscode/vsce or export in the PATH. Details can be found in INSTALL.md'
endif
