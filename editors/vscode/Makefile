world: compile
	#node_modules/.bin/vsce package

clean:
	rm -rf node_modules/ out/

VSCODE_DIR=~/.vscode/extensions
VSCODE_LP=$(VSCODE_DIR)/lp-vscode
node_modules:
	npm install
	rm -f $(VSCODE_LP)
	mkdir -p $(VSCODE_DIR)
	ln -sf `pwd` $(VSCODE_LP)

compile: node_modules
	npm run compile
