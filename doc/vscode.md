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

Typing ```@letter``` will suggest a corresponding unicode greek letter (for instance "@b" will suggest β). 

---

###   Fonts

- ```@letterletter```(for instance @nn): double-struck letter (ℕ)

- ```@itletter```(@itn): italic letter (𝑁)

- ```@ibletter```(@bin): italic bold (𝑵)

- ```@scletter```(@scn): script letter (𝒩 )

- ```@bsletter```(@bsn): bold script letter (𝓝)

- ```@frletter```(@frn): Fraktur letter (𝔑)

---

###   Common symbols

- ```@or``` : ∨

- ```@and``` : ∧

- ```@neg``` : ¬

- ```@imp```: ⇒

- ```@ar```: →

- ```@ho```: ↪

- ```@set```: ≔

- ```@eq```: ≡

- ```@as```: ⊢

- ```@fa```: ∀

- ```@ex```: ∃

- ```@imp```: ⇒

- ```@box```: □

- ```@tf```: ⸬



# Keybindings

For proof navigation :

- ```Ctrl+Down``` : go one step forward
- ```Ctrl+Up``` : go one step backward
- ```Ctrl+Enter``` : go to the position of the cursor
- ```Ctrl+Alt+c``` : toggle cursor mode (proof state follows the cursor or not)
