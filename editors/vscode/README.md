VSCode extension for Lambdapi
=============================

Usage
-----

See the [user manual](https://lambdapi.readthedocs.io/en/latest/ui/vscode.html>).

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
npm install
npm run compile
```

- create a VSCE package:

```bash
vsce package # creates the file lambdapi-0.1.0.vsix
```
