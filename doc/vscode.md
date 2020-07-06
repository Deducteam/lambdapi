Editing lambdapi source code with [VSCode](https://code.visualstudio.com/)
-------------------------------------

There is an extension for VSCode >= 1.37 derived from VSCoq. To
install it do from the `lambdapi` repository:

```bash
cd editors/vscode/
make clean
make
```

This requires to have `npm` and `node-typescript` installed:

```bash
sudo apt install npm node-typescript
```

_note_: as of today the vscode mode requires a full lambdapi install,
it won't unfortunately run from a developer tree.
