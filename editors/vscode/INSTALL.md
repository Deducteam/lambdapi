Installation from the sources
-----------------------------

- download `$node_file.tar.xz` from [node.js](https://nodejs.org/)

- extract node:

```bash
sudo apt-get install jq xz-utils
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

Please note that adding nodejs to the `$PATH` by executing the `export` commands from the terminal will make it work only in the terminal where these commands have been run. 

Thus, you need to re-execute them each time you work from a new terminal.
If you intend to do this often, it is recomanded to add the two `export` commands to your `~/.bashrc` or `~/.profile` files and then apply changes with :
 ```bash
 source ~/.bashrc
 source ~/.profile
 ```

- install dependencies:

```bash
npm install -g @types/vscode
npm install -g @vscode/vsce # to create VSCE packages
```

- installing:

To install the lambdapi extension from the sources, please use the dedicated rule in the `Makefile` as follows:

```bash
make install_local
```

This rule uses `jq` to read the extension version from `package.json`. If `jq` is not installed, please, read version from `package.json` and export `VERSION` before calling `install_local`

```bash
VERSION=X.Y.Z make install_local
```

Alternatively, you can run the install manually step by step :

- compilation:

```bash
make
```

- create a VSCE package:

```bash
vsce package # creates the file lambdapi-$version.vsix
```

- install the extension:

```bash
code --install-extension lambdapi-$version.vsix
```

Uninstallation can be done from code: go to extensions (Ctrl+Shift+X),
chose lambdapi and click on uninstall.
