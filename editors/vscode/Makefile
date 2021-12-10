default:
	npm install
	npm run compile

clean:
	rm -rf node_modules out

# folder for VSCode extensions
VSCE_DIR=~/.vscode/extensions
install:
	ln -sf `pwd` $(VSCE_DIR)/lambdapi

uninstall:
	rm -f $(VSCE_DIR)/lambdapi

package:
	vsce package
