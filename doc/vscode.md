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

# Overview

This extension provides syntax highlighting, unicode characters easy insertion and proof navigation as in CoqIde or ProofGeneral.

It is still under development, thus might be incomplete and buggy.

# Features


##  Proof navigation

Goals are visualised in a panel on the right side of the editor.

- By default, goals are printed according to the current position of the cursor.

- By toggling off "cursor mode" with
```
Ctrl+Alt+C
```
$\hspace{0.8cm}$ you can navigate the proof with [keybindings](#keybindings).

##  Snippets

Typing "@letter" will suggest a corresponding unicode greek letter (for instance "@b" will suggest β). Press Enter or Tab to confirm adding the Unicode character.

# Keybindings

- Toggle cursor mode
```
Ctrl+Alt+C
```

- Navigate down : go forward in the proof

```
Ctrl+Alt+S
```

- Navigate up : go backwards in the proof

```
Ctrl+Alt+Z
```
