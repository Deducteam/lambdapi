default: compile

clean:
	rm -rf node_modules/ out/

LP-VSCODE=~/.vscode/extensions/lambdapi
.PHONY: node_modules
node_modules:
	npm install
	rm -f $(LP-VSCODE)
	ln -sf `pwd` $(LP-VSCODE)

compile: node_modules
	npm run compile
