default: compile

compile: node_modules
	npm run compile

node_modules:
	npm install

clean:
	rm -rf node_modules out

# folder for VSCode extensions
VSCE_DIR=~/.vscode/extensions
install: compile
	ln -sf `pwd` $(VSCE_DIR)/lambdapi

uninstall:
	rm -f $(VSCE_DIR)/lambdapi

package: node_modules
	vsce package
