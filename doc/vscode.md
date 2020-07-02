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
- "Cursor mode" can be toggled to navigate the proof with the cursor.

##  Snippets

Type the advised snippets described below, then press Enter or Tab to confirm adding the chosen Unicode character.

---

###   Greek letters

Typing ```"`letter"``` will suggest a corresponding unicode greek letter (for instance "`b" will suggest β). 

Some greek letters are present in a 'var' form as in LaTeX, accessible with ```"`vletter"``` (for instance, \`f will suggest ϕ and \`vf will suggest φ).

---

###   Fonts

- ```"`dletter"```(for instance `dn): double-struck letter (ℕ)

- ```"`iletter"```(`in): italic letter (𝑁)

- ```"`ibletter"```(`ibn): italic bold (𝑵)

- ```"`sletter"```(`sn): script letter (𝒩 )

- ```"`bsletter"```(`bsn): bold script letter (𝓝)

- ```"`fletter"```(`fn): Fraktur letter (𝔑)

---

###   Common symbols

- ```"`or"``` : ∨

- ```"`and"``` : ∧

- ```"`not"``` : ¬

- ```"`imp"```: ⇒

- ```"`ra"```: →

- ```"`re"```: ↪

- ```"`set"```: ≔

- ```"`eq"```: ≡

- ```"`th"```: ⊢

- ```"`all"```: ∀

- ```"`ex"```: ∃

- ```"`imp"```: ⇒

- ```"`box"```: □

- ```"`tf"```: ⸬

---

###   Recommended extension

[This extension](https://marketplace.visualstudio.com/items?itemName=GuidoTapia2.unicode-math-vscode) allows for replacing "\\->" with →, "\\`_1`" with the index ₁ and many other unicode characters by simply pressing Tab.

---

###   Troubleshoot

If snippet completion does not seem to work with the VS-Code Lambdapi Extension or the recommended extension, try pressing "Ctrl+Space" to see completion suggestions.

# Keybindings

For proof navigation :

- ```Ctrl+Down``` : go one step forward
- ```Ctrl+Up``` : go one step backward
- `Ctrl+Left` : go to the previous proof (or the beginning)
- `Ctrl+Right` : go to the next proof (or the end)
- ```Ctrl+Enter``` : go to the position of the cursor
- ```Ctrl+Alt+c``` : toggle cursor mode (proof highlight follows the cursor or not)
- `Ctrl+Alt+w` : toggle follow mode (proof highlight is always centered in the window when keybindings are pressed)
- `Shift+Alt+w` : center proof highlight in the current window


# Commands

Proof navigation is also accessible via the command menu `Ctrl+Shift+P` and searching "Lambdapi".

A command to restart the Lambdapi VS Code mode is available (can be useful in case of bugs).