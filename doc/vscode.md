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

- You can navigate the proof with [keybindings](#keybindings).
- 
- "Cursor mode" can be toggled to navigate the proff with the cursor.

##  Snippets

Typing "@letter" will suggest a corresponding unicode greek letter (for instance "@b" will suggest β). Press Enter or Tab to confirm adding the Unicode character.

# Keybindings

- Navigate down : go forward in the proof

```
Ctrl+Down
```

- Navigate up : go backwards in the proof

```
Ctrl+Up
```

- Toggle cursor mode
```
Ctrl+Alt+C
```