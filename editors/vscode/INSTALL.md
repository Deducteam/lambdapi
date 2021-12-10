Installation from the sources
-----------------------------

- download `$node_file.tar.xz` from [node.js](https://nodejs.org/)

- extract node:

```bash
sudo apt-get install xz-utils # if you do not have xz already installed
tar xfa $node_file.tar.xz # creates $node_dir
```

- add `$node_dir/bin` in your `$PATH`:

```bash
export PATH=$node_dir:$PATH
```

- add `$node_dir/lib/node_modules` in your `$NODE_PATH`:

```bash
export NODE_PATH=$node_dir/lib/node_modules:$NODE_PATH
```

- install dependencies:

```bash
npm install -g @types/vscode
npm install -g vsce # for creating VSCE packages only
```

- compilation:

```bash
make
```

- manual installation (for testing):

```bash
make install
```

The install script creates a symbolic link from
``~/.vscode/extensions/lambapi`` to the current directory. You can
override this link location [for example for ``vscodium``] by setting the
``VSCE_DIR`` environment variable:

```bash
VSCE_DIR=~/.vscodium/extensions make install
```

Package generation and publication
----------------------------------

See all the details [here](https://code.visualstudio.com/api/working-with-extensions/publishing-extension).

- create a VSCE package:

```bash
vsce package # creates the file lambdapi-$version.vsix
```

- check the rendering of README.md in some [Markdown viewer](https://codebeautify.org/markdown-viewer). It will be displayed in VSCode by going to extensions
(Ctrl+Shift+X) and by clicking on lambdapi.

- create a new Personal Access Token on [Azure](https://dev.azure.com/lambdapi/) and save it into a file.

- publish a new version of the VSCE package:

```bash
vsce login lambdapi # and paste the Personal Access Token
vsce publish [patch|minor|major]
```

The publisher page is [here](https://marketplace.visualstudio.com/manage/publishers/deducteam).
